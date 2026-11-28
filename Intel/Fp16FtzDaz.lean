-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.IeeeFp16Special

@[expose] public section

/-!
# FTZ and DAZ for the fp16 value path

Two hardware modes that the IEEE-class model leaves out are modelled here:

* **DAZ** (denormals are zero) flushes a subnormal input word to the signed
  zero before decoding,
* **FTZ** (flush to zero) flushes a finite result whose magnitude is below the
  smallest normal (`1024` units of `2 ^ -24`) to the signed zero.

`dazWord`, `ftzWord` and `ftzVal` are proved idempotent, are identities on
zeros, normals and the non-finite words, and the DAZ decode law
`decodeFull_daz` relates the two views.
-/

namespace IntelGpu

/-- A nonzero subnormal word (`expField = 0`, nonzero mantissa). -/
def isSubnormal (w : Fp16) : Bool :=
  decide (expField w = 0) && decide (mantField w ≠ 0)

/-- The signed zero word. -/
def signedZero (neg : Bool) : Fp16 := if neg then 0x8000 else 0x0000

/-- Denormals-are-zero on an input word. -/
def dazWord (w : Fp16) : Fp16 :=
  if isSubnormal w then signedZero (signBit w) else w

/-- Flush-to-zero on a word. -/
def ftzWord (w : Fp16) : Fp16 :=
  if isSubnormal w then signedZero (signBit w) else w

/-- Flush-to-zero on the finite value domain (units of `2 ^ -24`). -/
def ftzVal (v : SVal) : SVal :=
  if v.mag = 0 then v else if v.mag < 1024 then ⟨v.sign, 0⟩ else v

theorem isSubnormal_zero : isSubnormal 0 = false := by decide

theorem isSubnormal_negZero : isSubnormal 0x8000 = false := by decide

theorem isSubnormal_one : isSubnormal 0x0001 = true := by decide

theorem isSubnormal_max : isSubnormal 0x03FF = true := by decide

theorem isSubnormal_minNormal : isSubnormal 0x0400 = false := by decide

theorem signedZero_not_subnormal (b : Bool) : isSubnormal (signedZero b) = false := by
  cases b <;> decide

theorem dazWord_subnormal (w : Fp16) (h : isSubnormal w = true) :
    dazWord w = signedZero (signBit w) := by
  simp [dazWord, h]

theorem dazWord_other (w : Fp16) (h : isSubnormal w = false) : dazWord w = w := by
  simp [dazWord, h]

theorem dazWord_idem (w : Fp16) : dazWord (dazWord w) = dazWord w := by
  unfold dazWord
  by_cases h : isSubnormal w = true
  · simp [h, signedZero_not_subnormal]
  · have h' : isSubnormal w = false := by simpa using h
    simp [h']

theorem ftzWord_idem (w : Fp16) : ftzWord (ftzWord w) = ftzWord w := by
  unfold ftzWord
  by_cases h : isSubnormal w = true
  · simp [h, signedZero_not_subnormal]
  · have h' : isSubnormal w = false := by simpa using h
    simp [h']

/-- DAZ decoding: a subnormal word decodes as the signed zero. -/
theorem decodeFull_daz (w : Fp16) :
    decodeFull (dazWord w) =
      if isSubnormal w then .fin ⟨signBit w, 0⟩ else decodeFull w := by
  unfold dazWord
  by_cases h : isSubnormal w = true
  · simp only [h, ite_true]
    cases hs : signBit w <;> decide
  · have h' : isSubnormal w = false := by simpa using h
    simp [h']

theorem ftzVal_zero (v : SVal) (h : v.mag = 0) : ftzVal v = v := by
  simp [ftzVal, h]

theorem ftzVal_subnormal (v : SVal) (h0 : v.mag ≠ 0) (h : v.mag < 1024) :
    ftzVal v = ⟨v.sign, 0⟩ := by
  simp [ftzVal, h0, h]

theorem ftzVal_normal (v : SVal) (h : 1024 ≤ v.mag) : ftzVal v = v := by
  have h0 : v.mag ≠ 0 := by omega
  have hlt : ¬ v.mag < 1024 := by omega
  simp [ftzVal, h0, hlt]

theorem ftzVal_idem (v : SVal) : ftzVal (ftzVal v) = ftzVal v := by
  unfold ftzVal
  by_cases h0 : v.mag = 0
  · simp [h0]
  · by_cases h : v.mag < 1024
    · simp [h0, h]
    · simp [h0, h]

/-- The smallest subnormal flushes to zero under DAZ. -/
theorem daz_smallest : dazWord 0x0001 = 0 := by decide

/-- The largest subnormal flushes to zero under DAZ. -/
theorem daz_largest : dazWord 0x03FF = 0 := by decide

/-- The smallest normal survives DAZ. -/
theorem daz_minNormal : dazWord 0x0400 = 0x0400 := by decide

/-- Its decoded value flushes to zero under FTZ. -/
theorem ftz_smallest_value :
    ftzVal ⟨false, 1⟩ = ⟨false, 0⟩ := by decide

/-- The smallest normal value survives FTZ. -/
theorem ftz_minNormal_value :
    ftzVal ⟨false, 1024⟩ = ⟨false, 1024⟩ := by decide

end IntelGpu
