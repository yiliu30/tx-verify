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

theorem pack_low1_preserves49 (s : RealState) (j : Nat) :
    (stepLoop s (.mov e1Loop dst62a src61a)).regs 49 j = s.regs 49 j := by
  simpa [vaLoopAlias] using stepLoop_mov_preserves_reg (s := s) (e := e1Loop) (dst := dst62a)
    (src := src61a) (r := 49) (j := j) (by decide)

theorem pack_low2_preserves49 (s : RealState) (j : Nat) :
    (stepLoop s (.movMasked e2Loop dst62b src61b)).regs 49 j = s.regs 49 j := by
  simpa [vaLoopAlias] using stepLoop_movMasked_preserves_reg (s := s) (e := e2Loop) (dst := dst62b)
    (src := src61b) (r := 49) (j := j) (by decide)

theorem pack_high1_preserves49 (s : RealState) (j : Nat) :
    (stepLoop s (.mov e1Loop dst63a src61aHigh)).regs 49 j = s.regs 49 j := by
  simpa [vaLoopAlias] using stepLoop_mov_preserves_reg (s := s) (e := e1Loop) (dst := dst63a)
    (src := src61aHigh) (r := 49) (j := j) (by decide)

theorem pack_high2_preserves49 (s : RealState) (j : Nat) :
    (stepLoop s (.movMasked e2Loop dst63b src61bHigh)).regs 49 j = s.regs 49 j := by
  simpa [vaLoopAlias] using stepLoop_movMasked_preserves_reg (s := s) (e := e2Loop) (dst := dst63b)
    (src := src61bHigh) (r := 49) (j := j) (by decide)

theorem vaPackBoth_preserves49 (s : RealState) (j : Nat) :
    (runRealWith stepLoop (runRealWith stepLoop s vaPackLow) vaPackHigh).regs 49 j =
      s.regs 49 j := by
  unfold vaPackLow vaPackHigh runRealWith
  simp only [List.foldl_cons, List.foldl_nil]
  rw [pack_high2_preserves49, pack_high1_preserves49,
    pack_low2_preserves49, pack_low1_preserves49]

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

theorem vaLoopP3_packed_full (s : RealState) (ids : Nat → Addr) (sizeLo sizeHi : Word)
    (j : Nat) (hj : j < 24) (hid : ∀ l, s.regs 59 l = ids l)
    (hslo : low32 (s.regs 49 0) = sizeLo) (hshi : low32 (s.regs 49 1) = sizeHi) :
    (runRealWith stepLoop (runRealWith stepLoop (runRealWith stepLoop s vaPackLow) vaPackHigh)
        vaGuardBlock).preds 3 j =
      vaLoopGuard (ids j) (vaLoopSize sizeLo sizeHi) := by
  apply vaLoopP3_packed s ids sizeLo sizeHi j hj hid
  · rw [vaPackBoth_preserves49, hslo]
  · rw [vaPackBoth_preserves49, hshi]

end
end IntelGpu
