-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaLoopCounter

@[expose] public section

/-!
# The SYCL-TLA scalar comparisons

The mainloop exit condition is set by PC 1400,
`cmp (lt)f3.1, null, r1.11, r1.15`, and consumed by the predicated jump at
PC 1401, `(W&~f3.1) jmpi`. This module decodes the 28 predicated `cmp`
forms of the dump into a `TlaCmp` structure, gives them a flag-writing
semantics, and proves the loop instance: `f3.1` is set to `1` exactly when
`r1.11 < r1.15`.

`(eq)`, `(ne)`, `(lt)` and `(gt)` are modelled on the 32-bit words, with
`lt`/`gt` unsigned. The loop counters are non-negative, so signed and unsigned agree on the
instance proved here.
-/

namespace IntelGpu

structure TlaCmp where
  cond : String
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

/-- Does the opcode end in ` cmp`? -/
def endsWithCmp (op : String) : Bool :=
  match op.toList.reverse with
  | 'p' :: 'm' :: 'c' :: ' ' :: _ => true
  | _ => false

/-- The predicated `cmp` form: `(W[&flags]) cmp (C|M) (op)fN.M null A B`.
The full predicate text is kept in `cond`; conditional forms are recorded but
their flag write is not yet gated. -/
def parseTlaCmpInstr : TlaInstr → Option TlaCmp
  | .plain "cmp" (e :: dst :: _null :: a :: b :: _) =>
      match parseTlaExec e, parseCmpFlag dst, parseTlaSrc a, parseTlaSrc b with
      | some ex, some (p, n, sub), some l, some r =>
          some ⟨"", ex, p, n, sub, l, r⟩
      | _, _, _, _ => none
  | .predicated op (e :: dst :: _null :: a :: b :: _) =>
      if endsWithCmp op then
        match parseTlaExec e, parseCmpFlag dst, parseTlaSrc a, parseTlaSrc b with
        | some ex, some (p, n, sub), some l, some r =>
            some ⟨op, ex, p, n, sub, l, r⟩
        | _, _, _, _ => none
      else none
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

/-- Parse the flag condition of `(W&fN.M)`; `(W)` is unconditional. -/
def parseCondFlag (s : String) : Option (Nat × Nat) :=
  match splitAtChar '&' s.toList with
  | some (_, rest) =>
      match numRuns (String.ofList rest) with
      | [n, m] => some (n, m)
      | _ => none
  | none => none

/-- The flag condition of a comparison, if it is conditional. -/
def TlaCmp.condFlag (c : TlaCmp) : Option (Nat × Nat) :=
  parseCondFlag c.cond

/-- The unconditional flag write. -/
def TlaCmp.writeFlag (st : TlaState) (c : TlaCmp) : TlaState :=
  { st with flags := writeBank st.flags c.flag c.flagSub (if c.holds st then 1 else 0) }

/-- Write the comparison result into the destination flag. A conditional
comparison leaves the state unchanged when its guard flag is clear. -/
def TlaCmp.step (st : TlaState) (c : TlaCmp) : TlaState :=
  match c.condFlag with
  | some (n, m) => if st.flags n m = 0 then st else c.writeFlag st
  | none => c.writeFlag st

theorem TlaCmp.step_unconditional (st : TlaState) (c : TlaCmp)
    (h : c.condFlag = none) :
    TlaCmp.step st c = c.writeFlag st := by
  unfold TlaCmp.step
  rw [h]

theorem TlaCmp.step_cond_clear (st : TlaState) (c : TlaCmp) (n m : Nat)
    (h : c.condFlag = some (n, m)) (hclear : st.flags n m = 0) :
    TlaCmp.step st c = st := by
  unfold TlaCmp.step
  rw [h]
  simp [hclear]

/-- The plain `cmp` of the FMHA prefill prologue (`(lt)f3.1`). -/
def plainCmp : TlaCmp :=
  ⟨"", ⟨16, 0, true⟩, "lt", 3, 1,
    .reg ⟨4, 0, 0, 1, 1, 0⟩, .reg ⟨2, 0, 6, 0, 1, 0⟩⟩

/-- The plain comparison is unconditional. -/
theorem plainCmp_condFlag : plainCmp.condFlag = none := by
  decide

/-- The plain comparison compares the two source elements. -/
theorem plainCmp_holds (st : TlaState) :
    plainCmp.holds st = decide (st.regs 4 0 < st.regs 2 6) := by
  simp [plainCmp, TlaCmp.holds, TlaCmp.valL, TlaCmp.valR, readTlaSrcState, srcIndex]

/-- The plain comparison writes `f3.1` unconditionally. -/
theorem plainCmp_step (st : TlaState) :
    TlaCmp.step st plainCmp =
      { st with flags := writeBank st.flags 3 1 (if plainCmp.holds st then 1 else 0) } := by
  rw [TlaCmp.step_unconditional st plainCmp plainCmp_condFlag]
  simp [TlaCmp.writeFlag, plainCmp]

/-- The loop-exit comparison at PC 1400. -/
def loopCmp : TlaCmp where
  cond := "(W) cmp"
  exec := ⟨16, 0, true⟩
  pred := "lt"
  flag := 3
  flagSub := 1
  srcL := .reg ⟨1, 0, 11, 0, 1, 0⟩
  srcR := .reg ⟨1, 0, 15, 0, 1, 0⟩

set_option maxRecDepth 100000 in
/-- There are 28 predicated comparisons in the dump. -/
theorem realTlaGemmCmp_length : realTlaGemmCmp.length = 28 := by decide

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

theorem loopCmp_condFlag : loopCmp.condFlag = none := by decide

theorem loopCmp_holds (st : TlaState) :
    loopCmp.holds st = decide (st.regs 1 11 < st.regs 1 15) := by
  simp [loopCmp, TlaCmp.holds, TlaCmp.valL, TlaCmp.valR, readTlaSrcState, srcIndex]

theorem loopCmp_step_flags (st : TlaState) :
    (loopCmp.step st).flags 3 1 =
      (if st.regs 1 11 < st.regs 1 15 then 1 else 0) := by
  rw [TlaCmp.step_unconditional st loopCmp loopCmp_condFlag]
  unfold TlaCmp.writeFlag
  simp [loopCmp, TlaCmp.holds, TlaCmp.valL, TlaCmp.valR,
    readTlaSrcState, srcIndex, writeBank]

theorem loopCmp_step_flags_other (st : TlaState) (r j : Nat)
    (h : (r, j) ≠ (3, 1)) :
    (loopCmp.step st).flags r j = st.flags r j := by
  rw [TlaCmp.step_unconditional st loopCmp loopCmp_condFlag]
  unfold TlaCmp.writeFlag
  simp only [loopCmp, writeBank]
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
