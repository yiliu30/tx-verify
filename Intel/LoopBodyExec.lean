-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.VectorAddLoopProgram
public import Intel.VectorAddLoopBody
public import Intel.LoopDwordStep

@[expose] public section

/-!
# Executing the decoded loop-body slice

The four instructions at PC 21..24 of `vaLoopProgram` are exactly
`vaLoopBody`.  The loop interpreter `stepLoop` only special-cases the
`mov`/`movMasked` dword views, so on these four instructions it agrees with
`stepVAL`.  This module connects the decoded slice to the already-proved
load/add/store memory effect.
-/

namespace IntelGpu

noncomputable section

/-- The four decoded instructions at PC 21..24: both loads, the add and the store. -/
def vaLoopBodySlice : List RInstr := (vaLoopProgram.drop 21).take 4

/-- The decoded body slice is the transcribed loop body. -/
theorem vaLoopBodySlice_eq : vaLoopBodySlice = vaLoopBody := by
  unfold vaLoopBodySlice vaLoopProgram vaLoopBody
  decide

/-- On the loop body, `stepLoop` agrees with the uniform `stepVAL` semantics. -/
theorem vaLoopBody_stepLoop_eq (s : RealState) :
    runRealWith stepLoop s vaLoopBody = runVAL s vaLoopBody := by
  unfold vaLoopBody runVAL stepVAL runRealWith
  simp [stepLoop, stepVAL]

/-- The decoded PC 21..24 body stores each lane's sum at C[index]. -/
theorem vaLoopBodySlice_store_at (s : RealState) (aPtr bPtr cPtr : Addr)
    (idx : Nat → Addr) (h : VaLoopBodyPre s aPtr bPtr cPtr idx) (l : Nat)
    (hl : l < 32) (ha : aPtr.toNat % 4 = 0) (hb : bPtr.toNat % 4 = 0)
    (hc : cPtr.toNat % 4 = 0)
    (hab : aPtr.toNat + 4 * (idx l).toNat < 2 ^ 64)
    (hbb : bPtr.toNat + 4 * (idx l).toNat < 2 ^ 64)
    (hcb : cPtr.toNat + 4 * (idx l).toNat < 2 ^ 64)
    (hboundC : ∀ k, k < 32 → cPtr.toNat + 4 * (idx k).toNat < 2 ^ 64)
    (hdistinct : ∀ k, k < 32 → k ≠ l → cPtr.toNat / 4 + (idx k).toNat ≠
      cPtr.toNat / 4 + (idx l).toNat) :
    (runRealWith stepLoop s vaLoopBodySlice).mem
        (cPtr.toNat / 4 + (idx l).toNat) =
      s.mem (aPtr.toNat / 4 + (idx l).toNat) +
        s.mem (bPtr.toNat / 4 + (idx l).toNat) := by
  rw [vaLoopBodySlice_eq, vaLoopBody_stepLoop_eq]
  exact vaLoopBody_store_at s aPtr bPtr cPtr idx h l hl ha hb hc hab hbb hcb
    hboundC hdistinct

end

end IntelGpu
