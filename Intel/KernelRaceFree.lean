-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.LoopKernelEntry
public import Intel.MemoryLaws

@[expose] public section

/-!
# Cross-lane race freedom for the loop vector add

Stage 140's `vaLoop_kernel_pc0_mem` assumes a pointwise `hdistinct`: every
other lane's `C` word address differs from the current lane's. This module
proves that hypothesis from launch injectivity, so the kernel's write
footprint is pairwise disjoint rather than assumed pointwise.

The computed id is
`zext localSize * zext r0 + zeroExtend(localId l) + zext globalOffset`. The
`localSize`, `r0` and `globalOffset` terms do not depend on the lane, so
cancellation in the additive group of `BitVec 64` removes them without an
overflow hypothesis. Lean 4.35 has no `BitVec.add_left_cancel`, so
`bitVec_add_left_cancel` derives the same law from `BitVec.add_sub_cancel`.

- `vaLoopId_eq_iff`, `vaLoopId_injective`, `vaLoopId_injective_lanes`: the
  launch terms cancel, and injective local ids give injective lane ids.
- `vaLoopId_ne`, `vaLoopId_pairwise_distinct`: the 32-lane contrapositive and
  the duplicate-free mapped `range 32`.
- `vaLoopKernel_cAddress_ne`: distinct ids give distinct dword addresses;
  `vaLoopKernel_cByteAddr_div` identifies that dword with the aligned byte
  address `cPtr + 4 * id`.
- `WriteFootprint`, `PairwiseDisjoint`, `vaLoopKernel_writes_disjoint`: the 32
  lanes' `C` write footprints are pairwise disjoint, and
  `vaLoopKernel_stores_commute` is the corresponding store-commutation law.
- `vaLoop_kernel_pc0_mem_hdistinct` and `vaLoop_kernel_pc0_mem_of_laneDistinct`:
  stage 140's pointwise hypothesis and full memory theorem follow from
  `LaneIdsDistinct`.
- `laneIdsDistinct_const_zero_false` and
  `vaLoopId_not_injective_of_constant_localId`: duplicate local ids falsify the
  conclusion, so the injectivity hypothesis is necessary.

The race-freedom theorems use only `propext` and `Quot.sound`. The composed
stage-140 theorem also depends on the axioms already used by
`vaLoop_kernel_pc0_mem`: `Classical.choice` and the four `bv_decide`
certificate axioms recorded in the stage-140 module.
-/

namespace IntelGpu

/-! ## Lane ids -/

/-- The local ids of the 32 work-group lanes are pairwise distinct. -/
def LaneIdsDistinct (localId : Nat → BitVec 16) : Prop :=
  ∀ a b, a < 32 → b < 32 → localId a = localId b → a = b

/-- Cancellation on the left in `BitVec` addition. This is the law usually
called `BitVec.add_left_cancel`, which Lean 4.35 does not provide; it follows
from `BitVec.add_sub_cancel` and needs no overflow hypothesis. -/
theorem bitVec_add_left_cancel {w : Nat} {a b c : BitVec w}
    (h : a + b = a + c) : b = c := by
  have h1 : (a + b) - a = b := by
    rw [BitVec.add_comm a b, BitVec.add_sub_cancel]
  have h2 : (a + c) - a = c := by
    rw [BitVec.add_comm a c, BitVec.add_sub_cancel]
  have h' := congrArg (fun x => x - a) h
  rwa [h1, h2] at h'

/-- Cancellation on the right in `BitVec` addition. -/
theorem bitVec_add_right_cancel {w : Nat} {a b c : BitVec w}
    (h : a + c = b + c) : a = b := by
  simpa only [BitVec.add_sub_cancel] using congrArg (fun x => x - c) h

/-- The 32 lane indices are duplicate-free. `decide` avoids the
`Classical.choice` dependency of `List.nodup_range`. -/
theorem range32_nodup : (List.range 32).Nodup := by decide

/-- Zero extension from 16 to 64 bits is injective. -/
theorem zeroExtend16_64_injective {a b : BitVec 16}
    (h : a.zeroExtend 64 = b.zeroExtend 64) : a = b := by
  apply BitVec.eq_of_toNat_eq
  have h' := congrArg BitVec.toNat h
  simp only [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth] at h'
  have ha : a.toNat < 2 ^ 64 := by have := a.isLt; omega
  have hb : b.toNat < 2 ^ 64 := by have := b.isLt; omega
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h'

/-- The computed id is equal exactly when the zero-extended local ids are
equal: the launch-dependent terms cancel in `BitVec 64`. -/
theorem vaLoopId_eq_iff (localSize r0 globalOffset : Word)
    (localId : Nat → BitVec 16) (a b : Nat) :
    vaLoopId localSize r0 globalOffset localId a =
        vaLoopId localSize r0 globalOffset localId b ↔
      (localId a).zeroExtend 64 = (localId b).zeroExtend 64 := by
  constructor
  · intro heq
    have h1 : zext localSize * zext r0 + (localId a).zeroExtend 64 +
          zext globalOffset =
        zext localSize * zext r0 + (localId b).zeroExtend 64 +
          zext globalOffset := heq
    have h2 : zext localSize * zext r0 + (localId a).zeroExtend 64 =
        zext localSize * zext r0 + (localId b).zeroExtend 64 :=
      bitVec_add_right_cancel h1
    exact bitVec_add_left_cancel h2
  · intro h
    simp [vaLoopId, h]

/-- If `localId` is injective, so is the computed lane id. The 32-lane version
is `vaLoopId_injective_lanes`. -/
theorem vaLoopId_injective (localSize r0 globalOffset : Word)
    (localId : Nat → BitVec 16)
    (h : ∀ a b, localId a = localId b → a = b) :
    ∀ a b, vaLoopId localSize r0 globalOffset localId a =
      vaLoopId localSize r0 globalOffset localId b → a = b := by
  intro a b heq
  exact h a b (zeroExtend16_64_injective
    ((vaLoopId_eq_iff localSize r0 globalOffset localId a b).mp heq))

/-- The 32-lane version: injectivity is only needed inside the work-group. -/
theorem vaLoopId_injective_lanes (localSize r0 globalOffset : Word)
    (localId : Nat → BitVec 16) (h : LaneIdsDistinct localId) :
    ∀ a b, a < 32 → b < 32 →
      vaLoopId localSize r0 globalOffset localId a =
        vaLoopId localSize r0 globalOffset localId b → a = b := by
  intro a b ha hb heq
  exact h a b ha hb (zeroExtend16_64_injective
    ((vaLoopId_eq_iff localSize r0 globalOffset localId a b).mp heq))

/-- The contrapositive: distinct lanes have distinct ids. -/
theorem vaLoopId_ne (localSize r0 globalOffset : Word) (localId : Nat → BitVec 16)
    (h : LaneIdsDistinct localId) {a b : Nat} (ha : a < 32) (hb : b < 32)
    (hab : a ≠ b) :
    vaLoopId localSize r0 globalOffset localId a ≠
      vaLoopId localSize r0 globalOffset localId b := by
  intro heq
  exact hab (vaLoopId_injective_lanes localSize r0 globalOffset localId h a b ha hb heq)

/-- The list of the 32 lane ids has no duplicates. -/
theorem vaLoopId_pairwise_distinct (localSize r0 globalOffset : Word)
    (localId : Nat → BitVec 16) (h : LaneIdsDistinct localId) :
    ((List.range 32).map (vaLoopId localSize r0 globalOffset localId)).Nodup := by
  rw [List.nodup_iff_pairwise_ne]
  rw [List.pairwise_map]
  rw [List.Pairwise.imp_mem]
  refine List.Pairwise.imp ?_
    (List.Pairwise.imp_mem.mp (List.nodup_iff_pairwise_ne.mp range32_nodup))
  intro a b hab ha hb heq
  exact hab ha hb
    (vaLoopId_injective_lanes localSize r0 globalOffset localId h a b
      (List.mem_range.mp ha) (List.mem_range.mp hb) heq)

/-! ## C addresses and write footprints -/

/-- Distinct ids give distinct dword addresses. The alignment premise is the
launch's `cPtr.toNat % 4 = 0`; the inequality itself needs only cancellation. -/
theorem vaLoopKernel_cAddress_ne (cPtr : Addr) (x y : Addr)
    (_hc : cPtr.toNat % 4 = 0) (hxy : x ≠ y) :
    cPtr.toNat / 4 + x.toNat ≠ cPtr.toNat / 4 + y.toNat := by
  intro h
  exact hxy (BitVec.eq_of_toNat_eq (Nat.add_left_cancel h))

/-- With 4-byte alignment and no wrap, the dword address used by stage 140 is
the word index of the byte address `cPtr + 4 * id`. -/
theorem vaLoopKernel_cByteAddr_div (cPtr id : Addr)
    (hc : cPtr.toNat % 4 = 0)
    (hb : cPtr.toNat + 4 * id.toNat < 2 ^ 64) :
    (cPtr + (4 : Addr) * id).toNat / 4 = cPtr.toNat / 4 + id.toNat := by
  have h4lt : 4 * id.toNat < 2 ^ 64 := by omega
  have hmul : ((4 : Addr) * id).toNat = 4 * id.toNat := by
    rw [BitVec.toNat_mul]
    rw [show ((4 : Addr).toNat) = 4 from by decide]
    rw [Nat.mod_eq_of_lt h4lt]
  have hadd : (cPtr + (4 : Addr) * id).toNat = cPtr.toNat + 4 * id.toNat := by
    rw [BitVec.toNat_add, hmul]
    exact Nat.mod_eq_of_lt hb
  have hq : cPtr.toNat = 4 * (cPtr.toNat / 4) := by
    have h := Nat.div_add_mod cPtr.toNat 4
    rw [hc, Nat.add_zero] at h
    exact h.symm
  rw [hadd]
  have hnum : cPtr.toNat + 4 * id.toNat =
      4 * (cPtr.toNat / 4) + 4 * id.toNat :=
    congrArg (fun x => x + 4 * id.toNat) hq
  rw [hnum, ← Nat.mul_add, Nat.mul_div_right _ (by decide : 0 < 4)]

/-- The dword address lane `l` writes in `C`. -/
def vaLoopCWordAddr (cPtr : Addr) (localSize r0 globalOffset : Word)
    (localId : Nat → BitVec 16) (l : Nat) : Nat :=
  cPtr.toNat / 4 + (vaLoopId localSize r0 globalOffset localId l).toNat

/-- The write footprint of the 32 lanes: one dword per lane. -/
abbrev WriteFootprint (cPtr : Addr) (localSize r0 globalOffset : Word)
    (localId : Nat → BitVec 16) : Nat → Nat :=
  vaLoopCWordAddr cPtr localSize r0 globalOffset localId

/-- Lane write footprints are pairwise disjoint on a window of `n` lanes. -/
def PairwiseDisjoint (n : Nat) (footprint : Nat → Nat) : Prop :=
  ∀ k l, k < n → l < n → k ≠ l → footprint k ≠ footprint l

/-- The 32 lanes' `C` write footprints are pairwise disjoint. -/
theorem vaLoopKernel_writes_disjoint (cPtr : Addr) (localSize r0 globalOffset : Word)
    (localId : Nat → BitVec 16) (hc : cPtr.toNat % 4 = 0)
    (h : LaneIdsDistinct localId) :
    PairwiseDisjoint 32 (WriteFootprint cPtr localSize r0 globalOffset localId) := by
  intro k l hk hl hkl
  exact vaLoopKernel_cAddress_ne cPtr _ _ hc
    (vaLoopId_ne localSize r0 globalOffset localId h hk hl hkl)

/-- Stores to two lanes' disjoint write footprints commute. -/
theorem vaLoopKernel_stores_commute (m : Nat → Word) (cPtr : Addr)
    (localSize r0 globalOffset : Word) (localId : Nat → BitVec 16)
    (hc : cPtr.toNat % 4 = 0) (h : LaneIdsDistinct localId)
    (a b : Nat) (ha : a < 32) (hb : b < 32) (hab : a ≠ b) (va vb : Word) :
    store32
        (store32 m (4 * vaLoopCWordAddr cPtr localSize r0 globalOffset localId a) va)
        (4 * vaLoopCWordAddr cPtr localSize r0 globalOffset localId b) vb =
      store32
        (store32 m (4 * vaLoopCWordAddr cPtr localSize r0 globalOffset localId b) vb)
        (4 * vaLoopCWordAddr cPtr localSize r0 globalOffset localId a) va := by
  refine store32_store32_commute m _ _ _ _ ?_
  rw [Nat.mul_div_right _ (by decide : 0 < 4),
    Nat.mul_div_right _ (by decide : 0 < 4)]
  exact vaLoopKernel_writes_disjoint cPtr localSize r0 globalOffset localId hc h
    a b ha hb hab

/-! ## Discharging stage 140 -/

/-- Stage 140's pointwise `hdistinct` follows from 32-lane local-id
injectivity and the launch alignment. -/
theorem vaLoop_kernel_pc0_mem_hdistinct (cPtr : Addr) (localSize r0 globalOffset : Word)
    (localId : Nat → BitVec 16) (hc : cPtr.toNat % 4 = 0)
    (h : LaneIdsDistinct localId) (l : Nat) (hl : l < 32) :
    ∀ k, k < 32 → k ≠ l →
      cPtr.toNat / 4 + (vaLoopId localSize r0 globalOffset localId k).toNat ≠
        cPtr.toNat / 4 + (vaLoopId localSize r0 globalOffset localId l).toNat := by
  intro k hk hkl
  exact vaLoopKernel_cAddress_ne cPtr _ _ hc
    (vaLoopId_ne localSize r0 globalOffset localId h hk hl hkl)

/-- Stage 140 with its `hdistinct` hypothesis discharged by `LaneIdsDistinct`. -/
theorem vaLoop_kernel_pc0_mem_of_laneDistinct (s : RealState) (lane fuel : Nat)
    (localSize r0 globalOffset : Word) (localId : Nat → BitVec 16)
    (aPtr bPtr cPtr : Addr) (sizeLo sizeHi : Word) (l : Nat)
    (hlaunch : VaLoopLaunch s localSize r0 globalOffset localId)
    (hsize : VaLoopSizePre s sizeLo sizeHi)
    (h47 : s.regs 47 0 = aPtr) (h48 : s.regs 48 0 = bPtr)
    (h46 : s.regs 46 0 = cPtr) (h37 : s.regs 37 0 = vaLoopSize sizeLo sizeHi)
    (hl : l < 32) (ha : aPtr.toNat % 4 = 0) (hb : bPtr.toNat % 4 = 0)
    (hc : cPtr.toNat % 4 = 0)
    (hab : aPtr.toNat + 4 * (vaLoopId localSize r0 globalOffset localId l).toNat < 2 ^ 64)
    (hbb : bPtr.toNat + 4 * (vaLoopId localSize r0 globalOffset localId l).toNat < 2 ^ 64)
    (hcb : cPtr.toNat + 4 * (vaLoopId localSize r0 globalOffset localId l).toNat < 2 ^ 64)
    (hboundC : ∀ k, k < 32 →
      cPtr.toNat + 4 * (vaLoopId localSize r0 globalOffset localId k).toNat < 2 ^ 64)
    (hlanes : LaneIdsDistinct localId)
    (hP3 : vaLoopGuard (vaLoopId localSize r0 globalOffset localId lane)
      (vaLoopSize sizeLo sizeHi) = true)
    (hj : lane < 24)
    (hbound : (vaLoopId localSize r0 globalOffset localId lane).toNat +
      (vaLoopSize sizeLo sizeHi).toNat < 2 ^ 64) :
    (runRealCFLaneWith stepLoop vaLoopProgram s 0 (fuel + 8 + 28) lane).mem
        (cPtr.toNat / 4 + (vaLoopId localSize r0 globalOffset localId l).toNat) =
      s.mem (aPtr.toNat / 4 + (vaLoopId localSize r0 globalOffset localId l).toNat) +
        s.mem (bPtr.toNat / 4 + (vaLoopId localSize r0 globalOffset localId l).toNat) := by
  exact vaLoop_kernel_pc0_mem s lane fuel localSize r0 globalOffset localId
    aPtr bPtr cPtr sizeLo sizeHi l hlaunch hsize h47 h48 h46 h37 hl ha hb hc
    hab hbb hcb hboundC
    (vaLoop_kernel_pc0_mem_hdistinct cPtr localSize r0 globalOffset localId hc hlanes l hl)
    hP3 hj hbound

/-! ## Injectivity is necessary -/

/-- A constant local id is not distinct on the 32-lane work-group. -/
theorem laneIdsDistinct_const_zero_false : ¬ LaneIdsDistinct (fun _ : Nat => 0) := by
  intro h
  have h01 : (0 : Nat) = 1 := h 0 1 (by decide) (by decide) rfl
  omega

/-- Two lanes of a constant local id compute the same address. -/
theorem vaLoopId_not_injective_of_constant_localId (localSize r0 globalOffset : Word) :
    ¬ Function.Injective
      (vaLoopId localSize r0 globalOffset (fun _ : Nat => (0 : BitVec 16))) := by
  intro h
  exact Nat.zero_ne_one (h rfl)

/-- The general claim without any injectivity hypothesis is false. -/
theorem vaLoopId_not_injective_without_laneDistinct :
    ¬ ∀ (localSize r0 globalOffset : Word) (localId : Nat → BitVec 16),
        Function.Injective (vaLoopId localSize r0 globalOffset localId) := by
  intro h
  exact Nat.zero_ne_one (h 0 0 0 (fun _ => 0) rfl)

end IntelGpu
