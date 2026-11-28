-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.RealSemantics

@[expose] public section

/-!
# Byte-addressed memory

Stage 1 models memory as one 32-bit word per aligned address. This module adds
the byte layer the review asks for:

- `load32LE` / `store32LE`: little-endian 32-bit accesses over `Nat → Byte`.
- `load32LE_store32LE_same`: a load sees its own store.
- `store32LE_frame`: bytes outside `[a, a+3]` are unchanged.
- `load32LE_store32LE_other`: a load is unchanged by a store to a disjoint
  four-byte range.
- `wordView_store32LE`: an aligned byte store is exactly a word store in the
  stage-1 view.

`byteDisjoint` is the byte-range aliasing predicate. `realAddOne_byteRangesDisjoint`
proves the real add-one kernel's 32 lane ranges are pairwise disjoint whenever
their word indices are distinct, so the stage-64 race-freedom hypothesis
refines to byte granularity. `realAddOne_byte_word_increment` reads the final
word through the byte view.
-/

namespace IntelGpu

abbrev Byte := BitVec 8

abbrev ByteMem := Nat → Byte

/-- Little-endian 32-bit load from four bytes. -/
def load32LE (m : ByteMem) (a : Nat) : Word :=
  BitVec.ofNat 32 ((m a).toNat + (m (a + 1)).toNat * 256 +
    (m (a + 2)).toNat * 65536 + (m (a + 3)).toNat * 16777216)

/-- Little-endian 32-bit store: four bytes at `a`, `a+1`, `a+2`, `a+3`. -/
def store32LE (m : ByteMem) (a : Nat) (v : Word) : ByteMem :=
  fun i =>
    if i = a then BitVec.ofNat 8 (v.toNat % 256)
    else if i = a + 1 then BitVec.ofNat 8 (v.toNat / 256 % 256)
    else if i = a + 2 then BitVec.ofNat 8 (v.toNat / 65536 % 256)
    else if i = a + 3 then BitVec.ofNat 8 (v.toNat / 16777216 % 256)
    else m i

@[simp] theorem byte_toNat (n : Nat) : (BitVec.ofNat 8 n).toNat = n % 256 := by
  rw [BitVec.toNat_ofNat]

theorem load32LE_store32LE_same (m : ByteMem) (a : Nat) (v : Word) :
    load32LE (store32LE m a v) a = v := by
  unfold load32LE store32LE
  have h1 : a + 1 ≠ a := by omega
  have h2 : a + 2 ≠ a := by omega
  have h3 : a + 3 ≠ a := by omega
  have h4 : a + 2 ≠ a + 1 := by omega
  have h5 : a + 3 ≠ a + 1 := by omega
  have h6 : a + 3 ≠ a + 2 := by omega
  simp only [h1, h2, h3, h4, h5, h6, ite_false, ite_true]
  rw [byte_toNat, byte_toNat, byte_toNat, byte_toNat]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  omega

theorem store32LE_frame (m : ByteMem) (a : Nat) (v : Word) (i : Nat)
    (h : i ≠ a ∧ i ≠ a + 1 ∧ i ≠ a + 2 ∧ i ≠ a + 3) :
    store32LE m a v i = m i := by
  rcases h with ⟨h0, h1, h2, h3⟩
  simp [store32LE, h0, h1, h2, h3]

theorem load32LE_store32LE_other (m : ByteMem) (a b : Nat) (v : Word)
    (h : b + 3 < a ∨ a + 3 < b) :
    load32LE (store32LE m a v) b = load32LE m b := by
  unfold load32LE
  have e0 : store32LE m a v b = m b :=
    store32LE_frame m a v b (by refine ⟨?_, ?_, ?_, ?_⟩ <;> omega)
  have e1 : store32LE m a v (b + 1) = m (b + 1) :=
    store32LE_frame m a v (b + 1) (by refine ⟨?_, ?_, ?_, ?_⟩ <;> omega)
  have e2 : store32LE m a v (b + 2) = m (b + 2) :=
    store32LE_frame m a v (b + 2) (by refine ⟨?_, ?_, ?_, ?_⟩ <;> omega)
  have e3 : store32LE m a v (b + 3) = m (b + 3) :=
    store32LE_frame m a v (b + 3) (by refine ⟨?_, ?_, ?_, ?_⟩ <;> omega)
  rw [e0, e1, e2, e3]

/-- The stage-1 word view of a byte memory. -/
def wordView (m : ByteMem) : Nat → Word := fun w => load32LE m (4 * w)

theorem wordView_store32LE (m : ByteMem) (w : Nat) (v : Word) :
    wordView (store32LE m (4 * w) v) = update (wordView m) w v := by
  funext w'
  by_cases h : w' = w
  · subst w'
    simp [wordView, update, load32LE_store32LE_same]
  · have hdisj : 4 * w' + 3 < 4 * w ∨ 4 * w + 3 < 4 * w' := by omega
    simp [wordView, update, h, load32LE_store32LE_other _ _ _ _ hdisj]

/-- Two four-byte ranges do not overlap. -/
def byteDisjoint (a b : Nat) : Prop := a + 3 < b ∨ b + 3 < a

/-- Aligned distinct word indices give disjoint byte ranges. -/
theorem wordDisjoint_byteDisjoint (a b : Addr) (ha : a.toNat % 4 = 0)
    (hb : b.toNat % 4 = 0) (h : a.toNat / 4 ≠ b.toNat / 4) :
    byteDisjoint a.toNat b.toNat := by
  unfold byteDisjoint
  omega

/-- Pairwise disjoint byte ranges for `n` lanes. -/
def byteRangesDisjoint (n : Nat) (addr : Nat → Nat) : Prop :=
  ∀ k l, k < n → l < n → k ≠ l → byteDisjoint (addr k) (addr l)

/-- The real add-one kernel's 32 write ranges are pairwise byte-disjoint. -/
theorem realAddOne_byteRangesDisjoint (base : Addr) (localSize r0 : Word)
    (localId : Nat → BitVec 16) (globalOffset : Word)
    (halign : base.toNat % 4 = 0)
    (hdistinct : ∀ k l, k < 32 → l < 32 → k ≠ l →
      (realAddress base (threadId localSize r0 localId globalOffset k)).toNat / 4 ≠
        (realAddress base (threadId localSize r0 localId globalOffset l)).toNat / 4) :
    byteRangesDisjoint 32
      (fun l => (realAddress base (threadId localSize r0 localId globalOffset l)).toNat) := by
  intro k l hk hl hkl
  exact wordDisjoint_byteDisjoint _ _
    (realAddress_aligned base _ halign)
    (realAddress_aligned base _ halign)
    (hdistinct k l hk hl hkl)

/-- An aligned byte load is a word-view read. -/
theorem load32LE_wordView (m : ByteMem) (a : Addr) (ha : a.toNat % 4 = 0) :
    load32LE m a.toNat = wordView m (a.toNat / 4) := by
  unfold wordView
  congr 1
  omega

/-- The real kernel's increment, read through a byte memory. -/
theorem realAddOne_byte_word_increment (s : RealState) (m : ByteMem) (base : Addr)
    (localSize r0 : Word) (localId : Nat → BitVec 16) (globalOffset : Word)
    (h : LaunchPre s base localSize r0 localId globalOffset)
    (halign : base.toNat % 4 = 0)
    (hview : s.mem = wordView m)
    (hdistinct : ∀ k l, k < 32 → l < 32 → k ≠ l →
      (realAddress base (threadId localSize r0 localId globalOffset k)).toNat / 4 ≠
        (realAddress base (threadId localSize r0 localId globalOffset l)).toNat / 4)
    (l : Nat) (hl : l < 32) :
    (runReal s realAddOneInstrs).mem
        ((realAddress base (threadId localSize r0 localId globalOffset l)).toNat / 4) =
      load32LE m
        (realAddress base (threadId localSize r0 localId globalOffset l)).toNat + 1 := by
  have heff := (realAddOne_effect s base localSize r0 localId globalOffset h halign
    hdistinct).2.2.1 l hl
  rw [heff, laneWord, hview,
    load32LE_wordView m _ (realAddress_aligned base _ halign)]

end IntelGpu
