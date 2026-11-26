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

end

end IntelGpu
