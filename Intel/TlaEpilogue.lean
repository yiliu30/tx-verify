-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaOnlineSoftmax

@[expose] public section

/-!
# Epilogue: normalising the running state

The flash-attention epilogue divides the running weighted value by the
running denominator. `onlineOut` is that division on the running state, and
`onlineOut_twoPass` rewrites it to the two-pass ratio at the state's own
maximum. The LSE variant additionally needs the `math.log` model and is left
to the conformance stage.
-/

namespace IntelGpu

/-- The normalised output of a running softmax state. -/
def onlineOut (st : OnlineState) : Rat := st.acc / st.l

/-- The LSE epilogue: the running maximum plus the log of the denominator. -/
def lseOut (logRef : Rat → Rat) (m l : Rat) : Rat := m + logRef l

/-- A one-element row recovers the logit exactly when log inverts exp. -/
theorem lseOut_single (logRef e : Rat → Rat) (h : ∀ x, logRef (e x) = x)
    (m x : Rat) : lseOut logRef m (e (x - m)) = x := by
  unfold lseOut
  rw [h, Rat.sub_eq_add_neg, ← Rat.add_assoc, Rat.add_comm m x, Rat.add_assoc,
    Rat.add_neg_cancel, Rat.add_zero]

/-- The running output is the two-pass ratio at the running maximum. -/
theorem onlineOut_twoPass (e : Rat → Rat) (st : OnlineState)
    (ps : List (Rat × Rat)) (hinv : OnlineInv e st ps) :
    onlineOut st = twoPassNum e st.m ps / twoPassDen e st.m ps := by
  rcases hinv with ⟨hl, ha⟩
  unfold onlineOut
  rw [ha, hl]

end IntelGpu
