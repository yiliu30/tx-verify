-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.LoopPackIncBoth
public import Intel.LoopP6Size
public import Intel.LoopGuard
public import Intel.LoopP3

@[expose] public section

/-!
# The second guard from the executed increment packs

Instantiate `vaLoopP6_guard` with the low/high halves produced by the real
increment pack sequence.
-/

namespace IntelGpu

noncomputable section

theorem vaLoopP6_packed (s : RealState) (ids : Nat → Addr) (sizeLo sizeHi : Word)
    (j : Nat) (hj : j < 24) (hid : ∀ l, s.regs 72 l = ids l)
    (hslo : low32 ((runRealWith stepLoop (runRealWith stepLoop s vaPackIncLow)
      vaPackIncHigh).regs 49 0) = sizeLo)
    (hshi : low32 ((runRealWith stepLoop (runRealWith stepLoop s vaPackIncLow)
      vaPackIncHigh).regs 49 1) = sizeHi) :
    (runRealWith stepLoop (runRealWith stepLoop (runRealWith stepLoop s vaPackIncLow)
        vaPackIncHigh) vaGuardBlock2).preds 6 j =
      vaLoopGuard (ids j) (vaLoopSize sizeLo sizeHi) := by
  let sP := runRealWith stepLoop (runRealWith stepLoop s vaPackIncLow) vaPackIncHigh
  have hpack := vaPackIncBoth_value s ids j hj hid
  have hslo' : low32 (sP.regs 49 0) = sizeLo := by simpa [sP] using hslo
  have hshi' : low32 (sP.regs 49 1) = sizeHi := by simpa [sP] using hshi
  rw [show runRealWith stepLoop sP vaGuardBlock2 = runVAL sP vaGuardBlock2 from by
    unfold vaGuardBlock2 runRealWith runVAL
    simp [stepLoop, runRealWith]]
  rw [vaLoopP6_guard sP j ((ids j).truncate 32) (((ids j) >>> 32).truncate 32)
    sizeLo sizeHi (by omega) (by simpa [sP] using hpack.1) (by simpa [sP] using hpack.2)
    hslo' hshi']
  rw [vaLoopSize_id]

theorem vaLoopP6_packed_full (s : RealState) (ids : Nat → Addr) (sizeLo sizeHi : Word)
    (j : Nat) (hj : j < 24) (hid : ∀ l, s.regs 72 l = ids l)
    (hslo : low32 (s.regs 49 0) = sizeLo) (hshi : low32 (s.regs 49 1) = sizeHi) :
    (runRealWith stepLoop (runRealWith stepLoop (runRealWith stepLoop s vaPackIncLow)
        vaPackIncHigh) vaGuardBlock2).preds 6 j =
      vaLoopGuard (ids j) (vaLoopSize sizeLo sizeHi) := by
  apply vaLoopP6_packed s ids sizeLo sizeHi j hj hid
  · rw [vaPackIncBoth_preserves49_low32, hslo]
  · rw [vaPackIncBoth_preserves49_low32, hshi]

end
end IntelGpu
