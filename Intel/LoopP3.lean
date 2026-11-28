-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.LoopPackBoth

@[expose] public section

/-!
# The first guard from the executed pack

Instantiate `vaLoopP3_guard` with the low/high halves produced by the real M1+M5
pack sequence.
-/

namespace IntelGpu

noncomputable section

theorem vaLoopSize_id (v : Addr) :
    vaLoopSize (v.truncate 32) ((v >>> 32).truncate 32) = v := by
  unfold vaLoopSize
  bv_decide

theorem stepLoop_guardBlock_eq (s : RealState) :
    runRealWith stepLoop s vaGuardBlock = runVAL s vaGuardBlock := by
  unfold vaGuardBlock runRealWith runVAL
  simp [stepLoop, runRealWith]

theorem vaLoopP3_packed (s : RealState) (ids : Nat → Addr) (sizeLo sizeHi : Word)
    (j : Nat) (hj : j < 24) (hid : ∀ l, s.regs 59 l = ids l)
    (hslo : low32 ((runRealWith stepLoop (runRealWith stepLoop s vaPackLow) vaPackHigh).regs 49 0)
      = sizeLo)
    (hshi : low32 ((runRealWith stepLoop (runRealWith stepLoop s vaPackLow) vaPackHigh).regs 49 1)
      = sizeHi) :
    (runRealWith stepLoop (runRealWith stepLoop (runRealWith stepLoop s vaPackLow) vaPackHigh)
        vaGuardBlock).preds 3 j =
      vaLoopGuard (ids j) (vaLoopSize sizeLo sizeHi) := by
  let sP := runRealWith stepLoop (runRealWith stepLoop s vaPackLow) vaPackHigh
  have hpack := vaPackBoth_value s ids j hj hid
  have hslo' : low32 (sP.regs 49 0) = sizeLo := by simpa [sP] using hslo
  have hshi' : low32 (sP.regs 49 1) = sizeHi := by simpa [sP] using hshi
  rw [show runRealWith stepLoop sP vaGuardBlock = runVAL sP vaGuardBlock from
    stepLoop_guardBlock_eq sP]
  rw [vaLoopP3_guard sP j ((ids j).truncate 32) (((ids j) >>> 32).truncate 32) sizeLo sizeHi
    (by omega) (by simpa [sP] using hpack.1) (by simpa [sP] using hpack.2) hslo' hshi']
  rw [vaLoopSize_id]

end
end IntelGpu
