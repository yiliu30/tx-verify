-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaBlock2dExec

@[expose] public section

/-!
# Scalar `math.exp` and `math.inv`

The FMHA prefill softmax uses 33 `math.exp` and one `math.inv` instruction.
Both are MUFU approximations, so the model separates the hardware function
from its contract:

* `MufuModel.exp`/`inv` are the bit-level functions the hardware applies;
* `toRat` reads a word as a rational, `expRef`/`invRef` are the reference
  functions, and `expErr`/`invErr` bound the approximation error;
* `exp_mono`/`inv_anti` record monotonicity of the hardware results.

The bounds are fields, not assumptions hidden in proofs: every downstream
theorem that needs an error budget takes the model as a parameter, so the
hardware contract is visible in the statement. `idMufu` is the degenerate
model used by machines that never execute a math instruction.
-/

namespace IntelGpu

inductive TlaMathOp where
  | exp | inv | log
  deriving Repr, DecidableEq

/-- A decoded `math.exp`/`math.inv`: `(16|M0) dst src`. -/
structure TlaMath where
  op : TlaMathOp
  exec : Exec
  dst : Grf
  src : TlaSrc
  deriving Repr, DecidableEq

def parseTlaMath : TlaInstr → Option TlaMath
  | .plain "math.exp" (e :: dst :: src :: _) =>
      match parseTlaExec e, parseTlaDst dst, parseTlaSrc src with
      | some ex, some (.reg g), some s => some ⟨.exp, ex, g, s⟩
      | _, _, _ => none
  | .plain "math.inv" (e :: dst :: src :: _) =>
      match parseTlaExec e, parseTlaDst dst, parseTlaSrc src with
      | some ex, some (.reg g), some s => some ⟨.inv, ex, g, s⟩
      | _, _, _ => none
  | .plain "math.log" (e :: dst :: src :: _) =>
      match parseTlaExec e, parseTlaDst dst, parseTlaSrc src with
      | some ex, some (.reg g), some s => some ⟨.log, ex, g, s⟩
      | _, _, _ => none
  | .predicated "(W) math.exp" (e :: dst :: src :: _) =>
      match parseTlaExec e, parseTlaDst dst, parseTlaSrc src with
      | some ex, some (.reg g), some s => some ⟨.exp, ex, g, s⟩
      | _, _, _ => none
  | .predicated "(W) math.inv" (e :: dst :: src :: _) =>
      match parseTlaExec e, parseTlaDst dst, parseTlaSrc src with
      | some ex, some (.reg g), some s => some ⟨.inv, ex, g, s⟩
      | _, _, _ => none
  | .predicated "(W) math.log" (e :: dst :: src :: _) =>
      match parseTlaExec e, parseTlaDst dst, parseTlaSrc src with
      | some ex, some (.reg g), some s => some ⟨.log, ex, g, s⟩
      | _, _, _ => none
  | _ => none

/-- The hardware MUFU model: bit functions plus rational references. -/
structure MufuModel where
  expFun : Word → Word
  invFun : Word → Word
  logFun : Word → Word
  toRat : Word → Rat
  expRef : Rat → Rat
  invRef : Rat → Rat
  logRef : Rat → Rat
  expErr : Rat
  invErr : Rat
  logErr : Rat

/-- The hardware contract: error bounds and monotonicity. -/
def MufuModel.Spec (m : MufuModel) : Prop :=
  (∀ x, Rat.abs (m.toRat (m.expFun x) - m.expRef (m.toRat x)) ≤ m.expErr) ∧
  (∀ x, m.toRat x ≠ 0 →
    Rat.abs (m.toRat (m.invFun x) - m.invRef (m.toRat x)) ≤ m.invErr) ∧
  (∀ (x y : Word), m.toRat x ≤ m.toRat y →
    m.toRat (m.expFun x) ≤ m.toRat (m.expFun y)) ∧
  (∀ (x y : Word), 0 < m.toRat x → m.toRat x ≤ m.toRat y →
    m.toRat (m.invFun y) ≤ m.toRat (m.invFun x)) ∧
  (∀ x, 0 < m.toRat x →
    Rat.abs (m.toRat (m.logFun x) - m.logRef (m.toRat x)) ≤ m.logErr)

/-- The degenerate model for machines without math instructions. -/
def idMufu : MufuModel where
  expFun := id
  invFun := id
  logFun := id
  toRat := fun _ => 0
  expRef := fun _ => 0
  invRef := fun _ => 0
  logRef := fun _ => 0
  expErr := 0
  invErr := 0
  logErr := 0

/-- The value of a math instruction at a lane. -/
def TlaMath.value (model : MufuModel) (rf : RegFile) (m : TlaMath) (i : Nat) : Word :=
  match m.op with
  | .exp => model.expFun (readTlaSrc rf m.src i)
  | .inv => model.invFun (readTlaSrc rf m.src i)
  | .log => model.logFun (readTlaSrc rf m.src i)

/-- Execute a math instruction. -/
def TlaMath.step (model : MufuModel) (rf : RegFile) (m : TlaMath) : RegFile :=
  writeTlaMasked rf m.dst m.exec (m.value model rf)

theorem TlaMath.step_value (model : MufuModel) (rf : RegFile) (m : TlaMath) (i : Nat)
    (hd1 : m.dst.hstride = 1) (ha : m.exec.elementActive i = true) :
    TlaMath.step model rf m m.dst.num (m.dst.dstIndex i) = m.value model rf i := by
  unfold TlaMath.step
  exact writeTlaMasked_element rf m.dst m.exec (m.value model rf) i hd1 ha

theorem TlaMath.step_frame (model : MufuModel) (rf : RegFile) (m : TlaMath)
    (r j : Nat) (hr : r ≠ m.dst.num) :
    TlaMath.step model rf m r j = rf r j := by
  unfold TlaMath.step
  unfold writeTlaMasked
  simp [hr]

/-- The `exp` error budget. -/
theorem MufuModel.exp_bound (m : MufuModel) (hm : m.Spec) (x : Word) :
    Rat.abs (m.toRat (m.expFun x) - m.expRef (m.toRat x)) ≤ m.expErr :=
  hm.1 x

/-- The `inv` error budget. -/
theorem MufuModel.inv_bound (m : MufuModel) (hm : m.Spec) (x : Word)
    (h : m.toRat x ≠ 0) :
    Rat.abs (m.toRat (m.invFun x) - m.invRef (m.toRat x)) ≤ m.invErr :=
  hm.2.1 x h

/-- `exp` is monotone on the represented values. -/
theorem MufuModel.exp_monotone (m : MufuModel) (hm : m.Spec) (x y : Word)
    (h : m.toRat x ≤ m.toRat y) :
    m.toRat (m.expFun x) ≤ m.toRat (m.expFun y) :=
  hm.2.2.1 x y h

set_option maxRecDepth 100000 in
/-- A synthetic `math.log` parses to the log op. -/
theorem parseTlaMath_log :
    parseTlaMath (.plain "math.log"
      ["(16|M0)", "r4.0<1>:f", "r4.0<1;1,0>:f", "{F@1}"]) =
      some ⟨.log, ⟨16, 0, true⟩, ⟨4, 0, 0, 1, 1, 1⟩,
        .reg ⟨4, 0, 0, 1, 1, 0⟩⟩ := by decide

/-- The `log` error budget. -/
theorem MufuModel.log_bound (m : MufuModel) (hm : m.Spec) (x : Word)
    (h : 0 < m.toRat x) :
    Rat.abs (m.toRat (m.logFun x) - m.logRef (m.toRat x)) ≤ m.logErr :=
  (hm.2.2.2).2 x h

/-- `inv` is antitone on the represented values. -/
theorem MufuModel.inv_antitone (m : MufuModel) (hm : m.Spec) (x y : Word)
    (hx : 0 < m.toRat x) (h : m.toRat x ≤ m.toRat y) :
    m.toRat (m.invFun y) ≤ m.toRat (m.invFun x) :=
  (hm.2.2.2).1 x y hx h

end IntelGpu
