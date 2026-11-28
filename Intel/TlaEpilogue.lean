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

/-- The running output is the two-pass ratio at the running maximum. -/
theorem onlineOut_twoPass (e : Rat → Rat) (st : OnlineState)
    (ps : List (Rat × Rat)) (hinv : OnlineInv e st ps) :
    onlineOut st = twoPassNum e st.m ps / twoPassDen e st.m ps := by
  rcases hinv with ⟨hl, ha⟩
  unfold onlineOut
  rw [ha, hl]

end IntelGpu
