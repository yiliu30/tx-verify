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

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

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


/-- The last iteration: the body plus `cmp.lt`, without the counter increment. -/
def gemmFinalStep : List RInstr :=
  gemmBodyBlock ++ [.cmpLt (Exec.nm 32) 1 ⟨79, 0, 0, 0, 1, 0⟩ 63 .ud]

theorem gemmFinalStep_sum (s : RealState) (aPtr bPtr cPtr : Addr)
    (i j0 k sum goX : Word) (l : Nat)
    (h : GemmLoopInv s aPtr bPtr cPtr l i j0 k sum goX)
    (hi : i.toNat < 64) (hk : k.toNat < 64) (hj0 : j0.toNat < 64)
    (hgoX : goX.toNat < 64)
    (ha : aPtr.toNat % 4 = 0)
    (hab : aPtr.toNat + 4 * (i * 64 + k).toNat < 2 ^ 64)
    (hb : bPtr.toNat % 4 = 0)
    (hbb : bPtr.toNat + 4 * (k * 64 + j0 + goX).toNat < 2 ^ 64) :
    (runGemm s gemmFinalStep).regs 62 l =
      zext (sum + gemmTerm s.mem (aPtr.toNat / 4) (bPtr.toNat / 4) i j0 goX k) := by
  have hj64 : j0.toNat % 2 ^ 64 = j0.toNat := Nat.mod_eq_of_lt (by omega)
  unfold gemmFinalStep gemmTerm runGemm
  rw [runRealWith_append]
  simp [runRealWith, gemmBodyBlock, stepGemm, stepWith, writeVecWith, setReg,
    readRegWith, readSrcWith, srcIndex, gemmAlias, isWideOf, gemmRegType,
    RegType.is64, binOpWide, add3Wide, shlWide, load32,
    h.v58, h.v61, h.v57, h.v62, h.aReg, h.bReg, h.goXReg,
    nat_or_shift_six_64 i k hi hk, shl_six, hj64, Nat.shiftLeft_eq]
  rw [nat_wordA aPtr i k hi hk ha hab,
    nat_wordB bPtr j0 k goX hk hj0 hgoX hb hbb]

theorem gemmFinalStep_pred (s : RealState) (aPtr bPtr cPtr : Addr)
    (i j0 k sum goX : Word) (l : Nat)
    (h : GemmLoopInv s aPtr bPtr cPtr l i j0 k sum goX) :
    (runGemm s gemmFinalStep).preds 1 0 = decide (k < 63) := by
  have h32 : (Exec.nm 32).size = 32 := rfl
  unfold gemmFinalStep runGemm
  rw [runRealWith_append]
  simp [h32, runRealWith, gemmBodyBlock, stepGemm, stepWith, writeVecWith, setReg,
    readRegWith, readSrcWith, srcIndex, gemmAlias, isWideOf, gemmRegType,
    RegType.is64, binOpWide, add3Wide, shlWide, load32, h.v61]

theorem gemmFinalStep_frame (s : RealState) (l w : Nat) :
    (runGemm s gemmFinalStep).regs 58 l = s.regs 58 l ∧
    (runGemm s gemmFinalStep).regs 57 l = s.regs 57 l ∧
    (runGemm s gemmFinalStep).regs 61 l = s.regs 61 l ∧
    (runGemm s gemmFinalStep).regs 34 l = s.regs 34 l ∧
    (runGemm s gemmFinalStep).regs 35 l = s.regs 35 l ∧
    (runGemm s gemmFinalStep).regs 36 l = s.regs 36 l ∧
    (runGemm s gemmFinalStep).regs 39 l = s.regs 39 l ∧
    (runGemm s gemmFinalStep).mem w = s.mem w := by
  unfold gemmFinalStep runGemm
  rw [runRealWith_append]
  simp [runRealWith, gemmBodyBlock, stepGemm, stepWith, writeVecWith, setReg,
    readRegWith, readSrcWith, srcIndex, gemmAlias, isWideOf, gemmRegType,
    RegType.is64, binOpWide, add3Wide, shlWide, load32]

theorem gemmFinalStep_inv (s : RealState) (aPtr bPtr cPtr : Addr)
    (i j0 k sum goX : Word) (l : Nat)
    (h : GemmLoopInv s aPtr bPtr cPtr l i j0 k sum goX)
    (hi : i.toNat < 64) (hk : k.toNat < 64) (hj0 : j0.toNat < 64)
    (hgoX : goX.toNat < 64)
    (ha : aPtr.toNat % 4 = 0)
    (hab : aPtr.toNat + 4 * (i * 64 + k).toNat < 2 ^ 64)
    (hb : bPtr.toNat % 4 = 0)
    (hbb : bPtr.toNat + 4 * (k * 64 + j0 + goX).toNat < 2 ^ 64) :
    GemmLoopInv (runGemm s gemmFinalStep) aPtr bPtr cPtr l i j0 k
        (sum + gemmTerm s.mem (aPtr.toNat / 4) (bPtr.toNat / 4) i j0 goX k)
        goX ∧
    (runGemm s gemmFinalStep).preds 1 0 = decide (k < 63) ∧
    (runGemm s gemmFinalStep).mem = s.mem := by
  have hf := gemmFinalStep_frame s l 0
  have hf0 := gemmFinalStep_frame s 0 0
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    gemmFinalStep_pred s aPtr bPtr cPtr i j0 k sum goX l h, ?_⟩
  · exact hf.1.trans h.v58
  · exact hf.2.1.trans h.v57
  · exact hf0.2.2.1.trans h.v61
  · exact gemmFinalStep_sum s aPtr bPtr cPtr i j0 k sum goX l h hi hk hj0 hgoX
      ha hab hb hbb
  · exact hf0.2.2.2.1.trans h.aReg
  · exact hf0.2.2.2.2.1.trans h.bReg
  · exact hf0.2.2.2.2.2.1.trans h.cReg
  · exact hf0.2.2.2.2.2.2.1.trans h.goXReg
  · funext w
    exact (gemmFinalStep_frame s l w).2.2.2.2.2.2.2


/-- The last term is appended at counter `k + n`. -/
theorem gemmDot_append (mem : Nat → Word) (aWord bWord : Nat) (i j0 goX : Word)
    (k : Word) (n : Nat) :
    gemmDot mem aWord bWord i j0 goX k (n + 1) =
      gemmDot mem aWord bWord i j0 goX k n +
        gemmTerm mem aWord bWord i j0 goX (k + BitVec.ofNat 32 n) := by
  induction n generalizing k with
  | zero => simp [gemmDot]
  | succ n ih =>
      rw [gemmDot_succ]
      conv =>
        rhs
        rw [gemmDot_succ]
      rw [ih (k + 1)]
      rw [BitVec.add_assoc, BitVec.add_assoc]
      simp only [BitVec.add_right_inj]
      congr 1
      bv_omega

/-- The full loop: 63 steps, the final body, the total `gemmDot 0 64`, and the
false exit predicate. -/
theorem gemmLoop_final (s : RealState) (aPtr bPtr cPtr : Addr)
    (i j0 goX : Word) (l : Nat)
    (h : GemmLoopInv s aPtr bPtr cPtr l i j0 0 0 goX)
    (hi : i.toNat < 64) (hj0 : j0.toNat < 64) (hgoX : goX.toNat < 64)
    (ha : aPtr.toNat % 4 = 0) (hb : bPtr.toNat % 4 = 0)
    (hboundA : ∀ kk : Word, kk.toNat < 64 →
      aPtr.toNat + 4 * (i * 64 + kk).toNat < 2 ^ 64)
    (hboundB : ∀ kk : Word, kk.toNat < 64 →
      bPtr.toNat + 4 * (kk * 64 + j0 + goX).toNat < 2 ^ 64) :
    GemmLoopInv (runGemm (gemmStepIter 63 s) gemmFinalStep) aPtr bPtr cPtr l i j0 63
        (gemmDot s.mem (aPtr.toNat / 4) (bPtr.toNat / 4) i j0 goX 0 64)
        goX ∧
    (runGemm (gemmStepIter 63 s) gemmFinalStep).preds 1 0 = false ∧
    (runGemm (gemmStepIter 63 s) gemmFinalStep).mem = s.mem := by
  have h63 := gemmStepIter_inv 63 s aPtr bPtr cPtr i j0 0 0 goX l h
    hi hj0 hgoX (by decide) ha hb hboundA hboundB
  have hk0 : (0 : Word) + BitVec.ofNat 32 63 = 63 := by bv_omega
  have hd0 : (0 : Word) + gemmDot s.mem (aPtr.toNat / 4) (bPtr.toNat / 4) i j0 goX 0 63 =
      gemmDot s.mem (aPtr.toNat / 4) (bPtr.toNat / 4) i j0 goX 0 63 := by
    simp
  rw [hk0, hd0] at h63
  have hk64 : (63 : Word).toNat < 64 := by decide
  have hfinal := gemmFinalStep_inv (gemmStepIter 63 s) aPtr bPtr cPtr i j0 63
    (gemmDot s.mem (aPtr.toNat / 4) (bPtr.toNat / 4) i j0 goX 0 63) goX l h63.1
    hi hk64 hj0 hgoX ha (hboundA _ hk64) hb (hboundB _ hk64)
  have happ := gemmDot_append s.mem (aPtr.toNat / 4) (bPtr.toNat / 4) i j0 goX 0 63
  have hk63 : (0 : Word) + BitVec.ofNat 32 63 = 63 := by bv_omega
  rw [hk63] at happ
  refine ⟨?_, ?_, ?_⟩
  · rw [happ]
    exact hfinal.1
  · simpa using hfinal.2.1
  · exact hfinal.2.2.trans h63.2


theorem gemmEpilogue_mem (s : RealState) :
    (runGemm s gemmEpilogue).mem =
      storeVec s.mem 32 ((runGemm s gemmEpilogue).regs 85)
        (fun l => low32 (s.regs 62 l)) := by
  unfold gemmEpilogue runGemm
  simp [runRealWith, stepGemm, stepWith, writeVecWith, setReg, readRegWith,
    readSrcWith, srcIndex, gemmAlias, isWideOf, gemmRegType, RegType.is64,
    binOpWide, add3Wide, shlWide]
  rfl

/-- The epilogue's store vector at a word index equal to lane `l`'s address
holds that lane's sum. -/
theorem gemmEpilogue_store_at (s : RealState) (aPtr bPtr cPtr : Addr)
    (i j0 k sum goX : Word) (l : Nat) (hl : l < 32) (w : Nat)
    (hw : w = (((runGemm s gemmEpilogue).regs 85) l).toNat / 4)
    (h : GemmLoopInv s aPtr bPtr cPtr l i j0 k sum goX)
    (hdistinct : ∀ l', l' < 32 → l' ≠ l →
      ((runGemm s gemmEpilogue).regs 85 l').toNat / 4 ≠
        ((runGemm s gemmEpilogue).regs 85 l).toNat / 4) :
    storeVec s.mem 32 ((runGemm s gemmEpilogue).regs 85)
        (fun l => low32 (s.regs 62 l)) w = sum := by
  subst hw
  have hs := storeVec_same s.mem 32 ((runGemm s gemmEpilogue).regs 85)
    (fun l => low32 (s.regs 62 l)) l hl hdistinct
  rw [h.v62] at hs
  simp at hs
  exact hs

/-- The final memory at lane `l`'s C word is that lane's sum. -/
theorem gemmEpilogue_store_mem (s : RealState) (aPtr bPtr cPtr : Addr)
    (i j0 k sum goX : Word) (l : Nat) (hl : l < 32) (w : Nat)
    (hw : w = (((runGemm s gemmEpilogue).regs 85) l).toNat / 4)
    (h : GemmLoopInv s aPtr bPtr cPtr l i j0 k sum goX)
    (hdistinct : ∀ l', l' < 32 → l' ≠ l →
      ((runGemm s gemmEpilogue).regs 85 l').toNat / 4 ≠
        ((runGemm s gemmEpilogue).regs 85 l).toNat / 4) :
    (runGemm s gemmEpilogue).mem w = sum := by
  rw [gemmEpilogue_mem]
  exact gemmEpilogue_store_at s aPtr bPtr cPtr i j0 k sum goX l hl w hw h hdistinct


theorem gemmEpilogue_halted (s : RealState) :
    (runGemm s gemmEpilogue).halted = true := by
  unfold gemmEpilogue runGemm
  simp [runRealWith, stepGemm, stepWith, writeVecWith, setReg, readRegWith,
    readSrcWith, srcIndex, gemmAlias, isWideOf, gemmRegType, RegType.is64,
    binOpWide, add3Wide, shlWide]

/-- The C byte address divided by four is the C word index. -/
theorem nat_wordC (cPtr : Addr) (i j0 goX : Word) (hc : cPtr.toNat % 4 = 0)
    (hbound : cPtr.toNat + 4 * (i * 64 + j0 + goX).toNat < 2 ^ 64) :
    (((zext (i * 64 + j0 + goX)) <<< 2 + cPtr).toNat / 4) =
      cPtr.toNat / 4 + (i * 64 + j0 + goX).toNat := by
  rw [show (zext (i * 64 + j0 + goX)) <<< 2 + cPtr =
      cPtr + (zext (i * 64 + j0 + goX)) <<< 2 from BitVec.add_comm _ _]
  exact wordOf_ptr_add_shift cPtr (i * 64 + j0 + goX) hc hbound

/-- The real GEMM's output: at lane `l`, the C word `w` holds the K-dot
product and the kernel has halted. -/
theorem realGemm_output (s : RealState) (aPtr bPtr cPtr : Addr)
    (i j0 goX : Word) (l : Nat) (hl : l < 32)
    (h : GemmLoopInv s aPtr bPtr cPtr l i j0 0 0 goX)
    (hi : i.toNat < 64) (hj0 : j0.toNat < 64) (hgoX : goX.toNat < 64)
    (ha : aPtr.toNat % 4 = 0) (hb : bPtr.toNat % 4 = 0) (hc : cPtr.toNat % 4 = 0)
    (hboundA : ∀ kk : Word, kk.toNat < 64 →
      aPtr.toNat + 4 * (i * 64 + kk).toNat < 2 ^ 64)
    (hboundB : ∀ kk : Word, kk.toNat < 64 →
      bPtr.toNat + 4 * (kk * 64 + j0 + goX).toNat < 2 ^ 64)
    (hboundC : cPtr.toNat + 4 * (i * 64 + j0 + goX).toNat < 2 ^ 64)
    (w : Nat) (hw : w = cPtr.toNat / 4 + (i * 64 + j0 + goX).toNat)
    (hdistinct : ∀ l', l' < 32 → l' ≠ l →
      ((runGemm (runGemm (gemmStepIter 63 s) gemmFinalStep) gemmEpilogue).regs 85 l').toNat / 4 ≠
        ((runGemm (runGemm (gemmStepIter 63 s) gemmFinalStep) gemmEpilogue).regs 85 l).toNat / 4) :
    (runGemm (runGemm (gemmStepIter 63 s) gemmFinalStep) gemmEpilogue).mem w =
        gemmDot s.mem (aPtr.toNat / 4) (bPtr.toNat / 4) i j0 goX 0 64 ∧
    (runGemm (runGemm (gemmStepIter 63 s) gemmFinalStep) gemmEpilogue).halted = true := by
  have hloop := gemmLoop_final s aPtr bPtr cPtr i j0 goX l h hi hj0 hgoX ha hb
    hboundA hboundB
  have haddr := gemmEpilogue_address (runGemm (gemmStepIter 63 s) gemmFinalStep)
    aPtr bPtr cPtr i j0 63 (gemmDot s.mem (aPtr.toNat / 4) (bPtr.toNat / 4) i j0 goX 0 64)
    goX l hloop.1
  have hw' : w = ((runGemm (runGemm (gemmStepIter 63 s) gemmFinalStep)
      gemmEpilogue).regs 85 l).toNat / 4 := by
    rw [haddr, nat_wordC cPtr i j0 goX hc hboundC]
    exact hw
  have hstore := gemmEpilogue_store_mem (runGemm (gemmStepIter 63 s) gemmFinalStep)
    aPtr bPtr cPtr i j0 63 (gemmDot s.mem (aPtr.toNat / 4) (bPtr.toNat / 4) i j0 goX 0 64)
    goX l hl w hw' hloop.1 hdistinct
  exact ⟨hstore, gemmEpilogue_halted _⟩

end

end IntelGpu




