-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.GemmReal

@[expose] public section

/-!
# The real GEMM loop, by induction

The one-iteration invariant is `gemmBodyStep_inv`. This module iterates it
without ever unfolding a whole program: `gemmStepIter n s` applies
`runGemm s gemmBodyStep` exactly `n` times.

`gemmTerm` is one dot-product term and `gemmDot` accumulates terms at
successive counters:

```
gemmDot k 0       = 0
gemmDot k (n + 1) = gemmTerm k + gemmDot (k + 1) n
```

`gemmStepIter_inv` proves the per-lane invariant after `n` steps, with the sum
advanced by `gemmDot`.
-/

namespace IntelGpu

noncomputable section

/-- `n` applications of the real loop step. -/
def gemmStepIter : Nat → RealState → RealState
  | 0, s => s
  | n + 1, s => gemmStepIter n (runGemm s gemmBodyStep)

/-- One dot-product term at counter `k`. -/
def gemmTerm (mem : Nat → Word) (aWord bWord : Nat) (i j0 goX : Word)
    (k : Word) : Word :=
  mem (aWord + (i * 64 + k).toNat) * mem (bWord + (k * 64 + j0 + goX).toNat)

/-- `n` terms starting at counter `k`. -/
def gemmDot (mem : Nat → Word) (aWord bWord : Nat) (i j0 goX : Word) :
    Word → Nat → Word
  | _, 0 => 0
  | k, n + 1 => gemmTerm mem aWord bWord i j0 goX k +
      gemmDot mem aWord bWord i j0 goX (k + 1) n

@[simp] theorem gemmStepIter_zero (s : RealState) : gemmStepIter 0 s = s := rfl

@[simp] theorem gemmStepIter_succ (n : Nat) (s : RealState) :
    gemmStepIter (n + 1) s = gemmStepIter n (runGemm s gemmBodyStep) := rfl

@[simp] theorem gemmDot_zero (mem : Nat → Word) (aWord bWord : Nat)
    (i j0 goX : Word) (_k : Word) :
    gemmDot mem aWord bWord i j0 goX _k 0 = 0 := rfl

theorem gemmDot_succ (mem : Nat → Word) (aWord bWord : Nat) (i j0 goX : Word)
    (k : Word) (n : Nat) :
    gemmDot mem aWord bWord i j0 goX k (n + 1) =
      gemmTerm mem aWord bWord i j0 goX k +
        gemmDot mem aWord bWord i j0 goX (k + 1) n := rfl

/-- After `n` real loop steps the per-lane invariant holds at `k + n` and the
sum has accumulated `n` terms. -/
theorem gemmStepIter_inv (n : Nat) (s : RealState) (aPtr bPtr cPtr : Addr)
    (i j0 k sum goX : Word) (l : Nat)
    (h : GemmLoopInv s aPtr bPtr cPtr l i j0 k sum goX)
    (hi : i.toNat < 64) (hj0 : j0.toNat < 64) (hgoX : goX.toNat < 64)
    (hkn : k.toNat + n ≤ 63)
    (ha : aPtr.toNat % 4 = 0) (hb : bPtr.toNat % 4 = 0)
    (hboundA : ∀ kk : Word, kk.toNat < 64 →
      aPtr.toNat + 4 * (i * 64 + kk).toNat < 2 ^ 64)
    (hboundB : ∀ kk : Word, kk.toNat < 64 →
      bPtr.toNat + 4 * (kk * 64 + j0 + goX).toNat < 2 ^ 64) :
    GemmLoopInv (gemmStepIter n s) aPtr bPtr cPtr l i j0
        (k + BitVec.ofNat 32 n)
        (sum + gemmDot s.mem (aPtr.toNat / 4) (bPtr.toNat / 4) i j0 goX k n)
        goX ∧
    (gemmStepIter n s).mem = s.mem := by
  induction n generalizing s k sum with
  | zero =>
      have hk0 : k + BitVec.ofNat 32 0 = k := by bv_omega
      rw [hk0]
      refine ⟨?_, rfl⟩
      simpa [gemmStepIter, gemmDot] using h
  | succ n ih =>
      rw [gemmStepIter_succ]
      have hk63 : k.toNat < 63 := by omega
      have hk64 : k.toNat < 64 := by omega
      have hstep := gemmBodyStep_inv s aPtr bPtr cPtr i j0 k sum goX l h hi hk63
        hj0 hgoX ha (hboundA _ hk64) hb (hboundB _ hk64)
      have hkn' : (k + 1).toNat + n ≤ 63 := by
        have : (k + 1).toNat = k.toNat + 1 := by bv_omega
        omega
      have hIH := ih (runGemm s gemmBodyStep) (k + 1)
        (sum + gemmTerm s.mem (aPtr.toNat / 4) (bPtr.toNat / 4) i j0 goX k)
        hstep.1 (by omega)
      have hk_eq : k + BitVec.ofNat 32 (n + 1) =
          (k + 1) + BitVec.ofNat 32 n := by bv_omega
      have hmem : (runGemm s gemmBodyStep).mem = s.mem := hstep.2.2
      rw [hmem] at hIH
      refine ⟨?_, ?_⟩
      · rw [hk_eq]
        simpa [gemmDot, BitVec.add_assoc] using hIH.1
      · exact hIH.2.trans hstep.2.2

end

end IntelGpu
