-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.VectorAddLoop
public import Intel.VectorAdd

@[expose] public section

/-!
# The loop vector add's load/add/store body

This module proves the memory effect of the four real instructions at
`_0_009`:

```
lsc_load.ugm V0069  flat(V0047)[4*V0059]
lsc_load.ugm V0070  flat(V0048)[4*V0059]
add          V0071  V0069 V0070
lsc_store.ugm flat(V0046)[4*V0059] V0071
```

It uses the real aliases/types from stage 104. The loop-carried pack/select
after the store is separate.
-/

namespace IntelGpu

noncomputable section

/-- A variant of `vaWordNat` with the reduced index expression produced by the
loop body's normal form. -/
theorem vaLoopWordNat (base idx : Nat) (hbase : base % 4 = 0)
    (hbound : base + 4 * idx < 2 ^ 64) :
    ((base + (idx <<< 2)) % 2 ^ 64) / 4 = base / 4 + idx := by
  have hmod : idx % 2 ^ 64 = idx := Nat.mod_eq_of_lt (by omega)
  simpa [hmod] using vaWordNat base idx hbase hbound

theorem vaLoopWordNat4 (base idx : Nat) (hbase : base % 4 = 0)
    (hbound : base + 4 * idx < 2 ^ 64) :
    ((base + idx * 4) % 2 ^ 64) / 4 = base / 4 + idx := by
  simpa [Nat.shiftLeft_eq] using vaLoopWordNat base idx hbase hbound

/-- The same word-index reduction for the bitvector expression printed by the
scaled memory semantics. -/
theorem vaLoopWordBitVec (base idx : Addr) (hbase : base.toNat % 4 = 0)
    (hbound : base.toNat + 4 * idx.toNat < 2 ^ 64) :
    (base + idx <<< 2).toNat / 4 = base.toNat / 4 + idx.toNat := by
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have hidx : BitVec.toNat idx * 2 ^ 2 % 2 ^ 64 = BitVec.toNat idx * 4 := by
    rw [show 2 ^ 2 = 4 by decide, Nat.mod_eq_of_lt]
    omega
  rw [hidx]
  exact vaLoopWordNat4 base.toNat idx.toNat hbase hbound

/-- The four memory instructions in the loop body. -/
def vaLoopBody : List RInstr :=
  [ .loadScaled 32 69 .d32 47 59,
    .loadScaled 32 70 .d32 48 59,
    .add 32 ⟨71, 0, 0, 1, 1, 1⟩ ⟨69, 0, 0, 1, 1, 0⟩ ⟨70, 0, 0, 1, 1, 0⟩,
    .storeScaled 32 46 59 .d32 71 ]

theorem realVectorAdd_body_prefix :
    (decodeRealProgram realVectorAdd).bind (fun is => (is.drop 21).take 4) =
      some vaLoopBody := by
  unfold decodeRealProgram decodeRealStmts realVectorAdd vaLoopBody
  decide

/-- The body's pointer and index registers. -/
structure VaLoopBodyPre (s : RealState) (aPtr bPtr cPtr : Addr)
    (idx : Nat → Addr) : Prop where
  aReg : s.regs 47 0 = aPtr
  bReg : s.regs 48 0 = bPtr
  cReg : s.regs 46 0 = cPtr
  idxReg : ∀ l, s.regs 59 l = idx l

/-- The preamble leaves the three pointer registers and memory unchanged. -/
theorem vaLoopPreamble_frame (s : RealState) :
    (runVAL s vaLoopPreamble).regs 46 0 = s.regs 46 0 ∧
    (runVAL s vaLoopPreamble).regs 47 0 = s.regs 47 0 ∧
    (runVAL s vaLoopPreamble).regs 48 0 = s.regs 48 0 ∧
    (runVAL s vaLoopPreamble).mem = s.mem := by
  unfold vaLoopPreamble runVAL stepVAL
  simp [runRealWith, stepWith, writeVecWith, setReg, vaLoopAlias]

/-- Launch facts plus the three pointers for the loop kernel. -/
structure VaLoopPre (s : RealState) (aPtr bPtr cPtr : Addr)
    (localSize r0 globalOffset : Word) (localId : Nat → BitVec 16) : Prop
    extends VaLoopLaunch s localSize r0 globalOffset localId where
  aReg : s.regs 47 0 = aPtr
  bReg : s.regs 48 0 = bPtr
  cReg : s.regs 46 0 = cPtr

theorem vaLoopPreamble_bodyPre (s : RealState) (aPtr bPtr cPtr : Addr)
    (localSize r0 globalOffset : Word) (localId : Nat → BitVec 16)
    (h : VaLoopPre s aPtr bPtr cPtr localSize r0 globalOffset localId) :
    VaLoopBodyPre (runVAL s vaLoopPreamble) aPtr bPtr cPtr
      (fun l => vaLoopId localSize r0 globalOffset localId l) := by
  rcases vaLoopPreamble_frame s with ⟨h46, h47, h48, _hmem⟩
  exact ⟨h47.trans h.aReg, h48.trans h.bReg, h46.trans h.cReg,
    fun l => vaLoopPreamble_id s localSize r0 globalOffset localId l h.toVaLoopLaunch⟩

/-- The body's memory is a store of the lane sums at the C addresses. -/
theorem vaLoopBody_mem (s : RealState) (aPtr bPtr cPtr : Addr)
    (idx : Nat → Addr) (h : VaLoopBodyPre s aPtr bPtr cPtr idx) :
    (runVAL s vaLoopBody).mem =
      storeVec s.mem 32
        (fun l => cPtr + (idx l) <<< 2)
        (fun l => low32 ((runVAL s vaLoopBody).regs 71 l)) := by
  unfold vaLoopBody runVAL stepVAL
  simp [runRealWith, stepWith, writeVecWith, setReg, readScalarWith,
    readRegWith, readSrcWith, srcIndex, vaLoopAlias, vaLoopRegType,
    isWideOf, RegType.is64, binOpWide, load32, h.aReg, h.bReg, h.cReg, h.idxReg]
  rfl

/-- The body's add produces the two loaded words at the lane's index. -/
theorem vaLoopBody_sum (s : RealState) (aPtr bPtr cPtr : Addr)
    (idx : Nat → Addr) (h : VaLoopBodyPre s aPtr bPtr cPtr idx) (l : Nat)
    (ha : aPtr.toNat % 4 = 0) (hb : bPtr.toNat % 4 = 0)
    (hab : aPtr.toNat + 4 * (idx l).toNat < 2 ^ 64)
    (hbb : bPtr.toNat + 4 * (idx l).toNat < 2 ^ 64) :
    low32 ((runVAL s vaLoopBody).regs 71 l) =
      s.mem (aPtr.toNat / 4 + (idx l).toNat) +
        s.mem (bPtr.toNat / 4 + (idx l).toNat) := by
  unfold vaLoopBody runVAL stepVAL
  simp [runRealWith, stepWith, writeVecWith, setReg, readScalarWith,
    readRegWith, readSrcWith, srcIndex, vaLoopAlias, vaLoopRegType,
    isWideOf, RegType.is64, binOpWide, load32, h.aReg, h.bReg, h.cReg, h.idxReg]
  rw [vaLoopWordNat aPtr.toNat (idx l).toNat ha hab,
    vaLoopWordNat bPtr.toNat (idx l).toNat hb hbb]

/-- The body stores each lane's sum at C[index]. -/
theorem vaLoopBody_store_at (s : RealState) (aPtr bPtr cPtr : Addr)
    (idx : Nat → Addr) (h : VaLoopBodyPre s aPtr bPtr cPtr idx) (l : Nat)
    (hl : l < 32) (ha : aPtr.toNat % 4 = 0) (hb : bPtr.toNat % 4 = 0)
    (hc : cPtr.toNat % 4 = 0)
    (hab : aPtr.toNat + 4 * (idx l).toNat < 2 ^ 64)
    (hbb : bPtr.toNat + 4 * (idx l).toNat < 2 ^ 64)
    (hcb : cPtr.toNat + 4 * (idx l).toNat < 2 ^ 64)
    (hboundC : ∀ k, k < 32 → cPtr.toNat + 4 * (idx k).toNat < 2 ^ 64)
    (hdistinct : ∀ k, k < 32 → k ≠ l → cPtr.toNat / 4 + (idx k).toNat ≠
      cPtr.toNat / 4 + (idx l).toNat) :
    (runVAL s vaLoopBody).mem (cPtr.toNat / 4 + (idx l).toNat) =
      s.mem (aPtr.toNat / 4 + (idx l).toNat) +
        s.mem (bPtr.toNat / 4 + (idx l).toNat) := by
  rw [vaLoopBody_mem s aPtr bPtr cPtr idx h]
  have hdistinct' : ∀ k, k < 32 → k ≠ l →
      (cPtr + (idx k) <<< 2).toNat / 4 ≠ (cPtr + (idx l) <<< 2).toNat / 4 := by
    intro k hk hne
    rw [vaLoopWordBitVec cPtr (idx k) hc (hboundC k hk),
      vaLoopWordBitVec cPtr (idx l) hc hcb]
    exact hdistinct k hk hne
  have hsame := storeVec_same s.mem 32 (fun l' => cPtr + (idx l') <<< 2)
    (fun l' => low32 ((runVAL s vaLoopBody).regs 71 l')) l hl hdistinct'
  rw [vaLoopWordBitVec cPtr (idx l) hc hcb] at hsame
  rw [hsame]
  exact vaLoopBody_sum s aPtr bPtr cPtr idx h l ha hb hab hbb

/-- End to end for one active lane of the real loop vector add: the preamble
computes the initial 64-bit id and the body stores `A[id] + B[id]` at `C[id]`. -/
theorem realVectorAdd_loop_effect (s : RealState) (aPtr bPtr cPtr : Addr)
    (localSize r0 globalOffset : Word) (localId : Nat → BitVec 16)
    (h : VaLoopPre s aPtr bPtr cPtr localSize r0 globalOffset localId)
    (l : Nat) (hl : l < 24) (ha : aPtr.toNat % 4 = 0) (hb : bPtr.toNat % 4 = 0)
    (hc : cPtr.toNat % 4 = 0)
    (hab : aPtr.toNat + 4 * (vaLoopId localSize r0 globalOffset localId l).toNat < 2 ^ 64)
    (hbb : bPtr.toNat + 4 * (vaLoopId localSize r0 globalOffset localId l).toNat < 2 ^ 64)
    (hcb : cPtr.toNat + 4 * (vaLoopId localSize r0 globalOffset localId l).toNat < 2 ^ 64)
    (hboundC : ∀ k, k < 32 → cPtr.toNat + 4 *
      (vaLoopId localSize r0 globalOffset localId k).toNat < 2 ^ 64)
    (hdistinct : ∀ k, k < 32 → k ≠ l →
      cPtr.toNat / 4 + (vaLoopId localSize r0 globalOffset localId k).toNat ≠
        cPtr.toNat / 4 + (vaLoopId localSize r0 globalOffset localId l).toNat) :
    (runVAL (runVAL s vaLoopPreamble) vaLoopBody).mem
        (cPtr.toNat / 4 + (vaLoopId localSize r0 globalOffset localId l).toNat) =
      s.mem (aPtr.toNat / 4 + (vaLoopId localSize r0 globalOffset localId l).toNat) +
        s.mem (bPtr.toNat / 4 + (vaLoopId localSize r0 globalOffset localId l).toNat) := by
  have hpre := vaLoopPreamble_bodyPre s aPtr bPtr cPtr localSize r0 globalOffset localId h
  have hstore := vaLoopBody_store_at (runVAL s vaLoopPreamble) aPtr bPtr cPtr
    (fun l => vaLoopId localSize r0 globalOffset localId l) hpre l (by omega) ha hb hc
    hab hbb hcb hboundC hdistinct
  simpa [vaLoopPreamble_mem s] using hstore

/-- After one body the index is at least `globalSize`, so the continuation
predicate is false. This range kernel therefore executes at most one body per
lane. -/
theorem vaLoopNext_not_lt (id : Addr) (size : Word)
    (hbound : id.toNat + size.toNat < 2 ^ 64) :
    ¬ (id + zext size).toNat < size.toNat := by
  intro h
  have hz : (zext size).toNat = size.toNat := by bv_omega
  rw [BitVec.toNat_add, hz, Nat.mod_eq_of_lt hbound] at h
  omega

/-- The 64-bit size assembled from the two dwords. -/
def vaLoopSize (lo hi : Word) : Addr :=
  (lo.zeroExtend 64) ||| ((hi.zeroExtend 64) <<< 32)

/-- The continuation guard used by the first compare. -/
def vaLoopGuard (id size : Addr) : Bool := decide (id < size)

theorem vaLoopNext_guard_false (id size : Addr)
    (hbound : id.toNat + size.toNat < 2 ^ 64) :
    vaLoopGuard (id + size) size = false := by
  unfold vaLoopGuard
  have h : ¬ (id + size).toNat < size.toNat := by
    intro hlt
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt hbound] at hlt
    omega
  by_cases hlt : (id + size) < size
  · exact (h hlt).elim
  · simp [hlt]

end

end IntelGpu
