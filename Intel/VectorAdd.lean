-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.RealSemantics
public import Intel.Examples.RealVectorAddFlat

@[expose] public section

/-!
# A real vector add: tables and the index preamble

`Intel/Examples/RealVectorAddFlat.lean` is the straight-line `nd_range` vector
add. This module instantiates the semantics with its `.decl` aliases and types
and proves the index computation

```
mul  V0052 = enqueuedLocalSize[0] * r0[1]
mov  V0053 = localIdX
add3 V0055 = V0052 + V0053 + globalOffset[0]
```
-/

namespace IntelGpu

noncomputable section

/-- The vector add's numeric aliases. -/
def vaAlias : Nat → Nat
  | 54 => 41
  | 56 => 35
  | 58 => 36
  | 61 => 34
  | n => n

/-- The vector add's declared register types. -/
def vaRegType : Nat → Option RegType
  | 34 => some .uq64
  | 35 => some .uq64
  | 36 => some .uq64
  | 37 => some .d32
  | 38 => some .d32
  | 39 => some .d32
  | 40 => some .d32
  | 41 => some .w16
  | 42 => some .w16
  | 43 => some .w16
  | 44 => some .uq64
  | 45 => some .uq64
  | 46 => some .d32
  | 47 => some .d32
  | 48 => some .d32
  | 49 => some .d32
  | 50 => some .d32
  | 51 => some .d32
  | 52 => some .d32
  | 53 => some .d32
  | 54 => some .uw16
  | 55 => some .d32
  | 56 => some .q64
  | 57 => some .d32
  | 58 => some .q64
  | 59 => some .d32
  | 60 => some .d32
  | 61 => some .q64
  | _ => none

/-- The vector add's declared element counts. -/
def vaRegElems : Nat → Nat
  | 34 => 1
  | 35 => 1
  | 36 => 1
  | 37 => 8
  | 38 => 8
  | 39 => 3
  | 40 => 3
  | 41 => 32
  | 42 => 32
  | 43 => 32
  | 44 => 1
  | 45 => 1
  | 46 => 1
  | 47 => 1
  | 48 => 1
  | 49 => 1
  | 50 => 1
  | 51 => 1
  | 52 => 1
  | 53 => 32
  | 54 => 32
  | 55 => 32
  | 56 => 1
  | 57 => 32
  | 58 => 1
  | 59 => 32
  | 60 => 32
  | 61 => 1
  | _ => 0

def stepVA : RealState → RInstr → RealState := stepWith vaAlias vaRegType

def runVA (s : RealState) (is : List RInstr) : RealState := runRealWith stepVA s is

/-- The first five statements: label, prologue, index arithmetic. -/
def vaPreamble : List RInstr :=
  [ .label "_main_0",
    .prologue,
    .mul 1 ⟨52, 0, 0, 1, 1, 0⟩ ⟨40, 0, 0, 0, 1, 0⟩ ⟨38, 0, 1, 0, 1, 0⟩,
    .mov 32 ⟨53, 0, 0, 1, 1, 0⟩ ⟨54, 0, 0, 1, 1, 0⟩,
    .add3 32 ⟨55, 0, 0, 1, 1, 0⟩ ⟨52, 0, 0, 0, 1, 0⟩ ⟨53, 0, 0, 1, 1, 0⟩
      ⟨39, 0, 0, 0, 1, 0⟩ ]

theorem realVectorAddFlat_preamble_prefix :
    (decodeRealProgram realVectorAddFlat).bind (fun is => is.take 5) = some vaPreamble := by
  unfold decodeRealProgram decodeRealStmts realVectorAddFlat vaPreamble
  decide

/-- The launch facts the vector add reads. -/
structure VaLaunch (s : RealState) (aPtr bPtr cPtr : Addr)
    (localSize r0 globalOffset : Word) (localId : Nat → BitVec 16) : Prop where
  aReg : s.regs 35 0 = aPtr
  bReg : s.regs 36 0 = bPtr
  cReg : s.regs 34 0 = cPtr
  localSizeReg : s.regs 40 0 = zext localSize
  r0Reg : s.regs 38 1 = zext r0
  localIdReg : ∀ l, s.regs 41 l = (localId l).zeroExtend 64
  offsetReg : s.regs 39 0 = zext globalOffset

/-- The global id, matching the source IR's `%10`. -/
def vaId (localSize r0 globalOffset : Word) (localId : Nat → BitVec 16)
    (l : Nat) : Word :=
  localSize * r0 + (localId l).zeroExtend 32 + globalOffset

/-- `V0055` is the global id. -/
theorem vaPreamble_id (s : RealState) (aPtr bPtr cPtr : Addr)
    (localSize r0 globalOffset : Word) (localId : Nat → BitVec 16)
    (h : VaLaunch s aPtr bPtr cPtr localSize r0 globalOffset localId) (l : Nat) :
    (runVA s vaPreamble).regs 55 l =
      zext (vaId localSize r0 globalOffset localId l) := by
  unfold vaPreamble runVA vaId
  simp [runRealWith, stepVA, stepWith, writeVecWith, setReg, readRegWith,
    readSrcWith, srcIndex, vaAlias, isWideOf, vaRegType, RegType.is64,
    binOpWide, add3Wide, h.localSizeReg, h.r0Reg, h.localIdReg, h.offsetReg]

/-- The whole straight-line vector add decodes, including the scaled loads and
store. -/
theorem realVectorAddFlat_decodes :
    (decodeRealProgram realVectorAddFlat).isSome = true := by
  unfold decodeRealProgram decodeRealStmts realVectorAddFlat
  decide

/-- One label and nine instructions. -/
theorem realVectorAddFlat_decoded_length :
    (decodeRealProgram realVectorAddFlat).map List.length = some 10 := by
  unfold decodeRealProgram decodeRealStmts realVectorAddFlat
  decide


/-- The preamble leaves the three pointer registers untouched. -/
theorem vaPreamble_pointers (s : RealState) :
    (runVA s vaPreamble).regs 35 0 = s.regs 35 0 ∧
    (runVA s vaPreamble).regs 36 0 = s.regs 36 0 ∧
    (runVA s vaPreamble).regs 34 0 = s.regs 34 0 := by
  unfold vaPreamble runVA
  simp [runRealWith, stepVA, stepWith, writeVecWith, setReg, readRegWith,
    readSrcWith, srcIndex, vaAlias, isWideOf, vaRegType, RegType.is64,
    binOpWide, add3Wide]

/-- The preamble does not write memory. -/
theorem vaPreamble_mem (s : RealState) :
    (runVA s vaPreamble).mem = s.mem := by
  unfold vaPreamble runVA
  simp [runRealWith, stepVA, stepWith, writeVecWith]

/-- The word index of a scaled address. -/
def vaWord (base : Addr) (idx : Word) : Nat :=
  (base + (zext idx) <<< 2).toNat / 4

theorem vaWord_eq (base : Addr) (idx : Word) (hbase : base.toNat % 4 = 0)
    (hbound : base.toNat + 4 * idx.toNat < 2 ^ 64) :
    vaWord base idx = base.toNat / 4 + idx.toNat := by
  unfold vaWord
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft]
  have hz : (zext idx).toNat = idx.toNat := by bv_omega
  rw [hz, Nat.shiftLeft_eq]
  omega

theorem vaWordNat (base idx : Nat) (hbase : base % 4 = 0)
    (hbound : base + 4 * idx < 2 ^ 64) :
    ((base + ((idx % 2 ^ 64) <<< 2)) % 2 ^ 64) / 4 = base / 4 + idx := by
  have hidx : idx % 2 ^ 64 = idx := Nat.mod_eq_of_lt (by omega)
  rw [hidx, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (by omega : base + idx * 4 < 2 ^ 64)]
  omega

/-- The tail of the vector add: two scaled loads, add, scaled store, return. -/
def vaTail : List RInstr :=
  [ .loadScaled 32 57 .d32 56 55,
    .loadScaled 32 59 .d32 58 55,
    .add 32 ⟨60, 0, 0, 1, 1, 0⟩ ⟨57, 0, 0, 1, 1, 0⟩ ⟨59, 0, 0, 1, 1, 0⟩,
    .storeScaled 32 61 55 .d32 60,
    .ret 1 ]

/-- The decoded program is the preamble followed by the tail. -/
theorem realVectorAddFlat_decoded_eq :
    decodeRealProgram realVectorAddFlat = some (vaPreamble ++ vaTail) := by
  unfold decodeRealProgram decodeRealStmts realVectorAddFlat vaPreamble vaTail
  decide

theorem vaLoadA (s : RealState) (aPtr bPtr cPtr : Addr)
    (localSize r0 globalOffset : Word) (localId : Nat → BitVec 16)
    (h : VaLaunch s aPtr bPtr cPtr localSize r0 globalOffset localId)
    (l : Nat) (ha : aPtr.toNat % 4 = 0)
    (hab : aPtr.toNat + 4 * (vaId localSize r0 globalOffset localId l).toNat < 2 ^ 64) :
    (runVA s (vaPreamble ++ vaTail)).regs 57 l =
      zext (s.mem (aPtr.toNat / 4 + (vaId localSize r0 globalOffset localId l).toNat)) := by
  have hp := vaPreamble_pointers s
  have hid := vaPreamble_id s aPtr bPtr cPtr localSize r0 globalOffset localId h l
  have hp35 : (List.foldl (stepWith vaAlias vaRegType) s vaPreamble).regs 35 0 = aPtr := by
    simpa [runVA, runRealWith, stepVA, h.aReg] using hp.1
  have hid' : (List.foldl (stepWith vaAlias vaRegType) s vaPreamble).regs 55 l =
      zext (vaId localSize r0 globalOffset localId l) := by
    simpa [runVA, runRealWith, stepVA] using hid
  have hmem' : (List.foldl (stepWith vaAlias vaRegType) s vaPreamble).mem = s.mem := by
    simpa [runVA, runRealWith, stepVA] using vaPreamble_mem s
  unfold vaTail runVA
  rw [runRealWith_append]
  simp [runRealWith, stepVA, stepWith, writeVecWith, setReg, readScalarWith,
    readRegWith, readSrcWith, srcIndex, vaAlias, isWideOf, vaRegType,
    RegType.is64, binOpWide, load32, hp35, hid', hmem']
  rw [vaWordNat aPtr.toNat (vaId localSize r0 globalOffset localId l).toNat ha hab]


theorem vaLoadB (s : RealState) (aPtr bPtr cPtr : Addr)
    (localSize r0 globalOffset : Word) (localId : Nat → BitVec 16)
    (h : VaLaunch s aPtr bPtr cPtr localSize r0 globalOffset localId)
    (l : Nat) (hb : bPtr.toNat % 4 = 0)
    (hbb : bPtr.toNat + 4 * (vaId localSize r0 globalOffset localId l).toNat < 2 ^ 64) :
    (runVA s (vaPreamble ++ vaTail)).regs 59 l =
      zext (s.mem (bPtr.toNat / 4 + (vaId localSize r0 globalOffset localId l).toNat)) := by
  have hp := vaPreamble_pointers s
  have hid := vaPreamble_id s aPtr bPtr cPtr localSize r0 globalOffset localId h l
  have hp36 : (List.foldl (stepWith vaAlias vaRegType) s vaPreamble).regs 36 0 = bPtr := by
    simpa [runVA, runRealWith, stepVA, h.bReg] using hp.2.1
  have hid' : (List.foldl (stepWith vaAlias vaRegType) s vaPreamble).regs 55 l =
      zext (vaId localSize r0 globalOffset localId l) := by
    simpa [runVA, runRealWith, stepVA] using hid
  have hmem' : (List.foldl (stepWith vaAlias vaRegType) s vaPreamble).mem = s.mem := by
    simpa [runVA, runRealWith, stepVA] using vaPreamble_mem s
  unfold vaTail runVA
  rw [runRealWith_append]
  simp [runRealWith, stepVA, stepWith, writeVecWith, setReg, readScalarWith,
    readRegWith, readSrcWith, srcIndex, vaAlias, isWideOf, vaRegType,
    RegType.is64, binOpWide, load32, hp36, hid', hmem']
  rw [vaWordNat bPtr.toNat (vaId localSize r0 globalOffset localId l).toNat hb hbb]

theorem vaAdd (s : RealState) (aPtr bPtr cPtr : Addr)
    (localSize r0 globalOffset : Word) (localId : Nat → BitVec 16)
    (h : VaLaunch s aPtr bPtr cPtr localSize r0 globalOffset localId)
    (l : Nat) (ha : aPtr.toNat % 4 = 0) (hb : bPtr.toNat % 4 = 0)
    (hab : aPtr.toNat + 4 * (vaId localSize r0 globalOffset localId l).toNat < 2 ^ 64)
    (hbb : bPtr.toNat + 4 * (vaId localSize r0 globalOffset localId l).toNat < 2 ^ 64) :
    (runVA s (vaPreamble ++ vaTail)).regs 60 l =
      zext (s.mem (aPtr.toNat / 4 + (vaId localSize r0 globalOffset localId l).toNat) +
        s.mem (bPtr.toNat / 4 + (vaId localSize r0 globalOffset localId l).toNat)) := by
  have hp := vaPreamble_pointers s
  have hid := vaPreamble_id s aPtr bPtr cPtr localSize r0 globalOffset localId h l
  have hp35 : (List.foldl (stepWith vaAlias vaRegType) s vaPreamble).regs 35 0 = aPtr := by
    simpa [runVA, runRealWith, stepVA, h.aReg] using hp.1
  have hp36 : (List.foldl (stepWith vaAlias vaRegType) s vaPreamble).regs 36 0 = bPtr := by
    simpa [runVA, runRealWith, stepVA, h.bReg] using hp.2.1
  have hid' : (List.foldl (stepWith vaAlias vaRegType) s vaPreamble).regs 55 l =
      zext (vaId localSize r0 globalOffset localId l) := by
    simpa [runVA, runRealWith, stepVA] using hid
  have hmem' : (List.foldl (stepWith vaAlias vaRegType) s vaPreamble).mem = s.mem := by
    simpa [runVA, runRealWith, stepVA] using vaPreamble_mem s
  unfold vaTail runVA
  rw [runRealWith_append]
  simp [runRealWith, stepVA, stepWith, writeVecWith, setReg, readScalarWith,
    readRegWith, readSrcWith, srcIndex, vaAlias, isWideOf, vaRegType,
    RegType.is64, binOpWide, load32, hp35, hp36, hid', hmem']
  rw [vaWordNat aPtr.toNat (vaId localSize r0 globalOffset localId l).toNat ha hab,
    vaWordNat bPtr.toNat (vaId localSize r0 globalOffset localId l).toNat hb hbb]


theorem vaTail_halted (s : RealState) :
    (runVA s vaTail).halted = true := by
  unfold vaTail runVA
  simp [runRealWith, stepVA, stepWith, writeVecWith, setReg, readScalarWith,
    readRegWith, readSrcWith, srcIndex, vaAlias, isWideOf, vaRegType,
    RegType.is64, binOpWide]


/-- The final memory is a store vector over the C addresses. -/
theorem vaMem (s : RealState) (aPtr bPtr cPtr : Addr)
    (localSize r0 globalOffset : Word) (localId : Nat → BitVec 16)
    (h : VaLaunch s aPtr bPtr cPtr localSize r0 globalOffset localId) :
    (runVA s (vaPreamble ++ vaTail)).mem =
      storeVec s.mem 32
        (fun l' => cPtr + (zext (vaId localSize r0 globalOffset localId l')) <<< 2)
        (fun l' => low32 ((runVA s (vaPreamble ++ vaTail)).regs 60 l')) := by
  have hp := vaPreamble_pointers s
  have hp35 : (List.foldl (stepWith vaAlias vaRegType) s vaPreamble).regs 35 0 = aPtr := by
    simpa [runVA, runRealWith, stepVA, h.aReg] using hp.1
  have hp36 : (List.foldl (stepWith vaAlias vaRegType) s vaPreamble).regs 36 0 = bPtr := by
    simpa [runVA, runRealWith, stepVA, h.bReg] using hp.2.1
  have hp34 : (List.foldl (stepWith vaAlias vaRegType) s vaPreamble).regs 34 0 = cPtr := by
    simpa [runVA, runRealWith, stepVA, h.cReg] using hp.2.2
  have hidAll : ∀ l', (List.foldl (stepWith vaAlias vaRegType) s vaPreamble).regs 55 l' =
      zext (vaId localSize r0 globalOffset localId l') := by
    intro l'
    simpa [runVA, runRealWith, stepVA] using
      vaPreamble_id s aPtr bPtr cPtr localSize r0 globalOffset localId h l'
  have hmem' : (List.foldl (stepWith vaAlias vaRegType) s vaPreamble).mem = s.mem := by
    simpa [runVA, runRealWith, stepVA] using vaPreamble_mem s
  unfold vaTail runVA
  rw [runRealWith_append]
  simp [runRealWith, stepVA, stepWith, writeVecWith, setReg, readScalarWith,
    readRegWith, readSrcWith, srcIndex, vaAlias, isWideOf, vaRegType,
    RegType.is64, binOpWide, load32, hp35, hp36, hp34, hidAll, hmem']

/-- The store writes each lane's `a[id] + b[id]` at its C word. -/
theorem vaStore (s : RealState) (aPtr bPtr cPtr : Addr)
    (localSize r0 globalOffset : Word) (localId : Nat → BitVec 16)
    (h : VaLaunch s aPtr bPtr cPtr localSize r0 globalOffset localId)
    (l : Nat) (hl : l < 32) (ha : aPtr.toNat % 4 = 0) (hb : bPtr.toNat % 4 = 0)
    (hc : cPtr.toNat % 4 = 0)
    (hab : aPtr.toNat + 4 * (vaId localSize r0 globalOffset localId l).toNat < 2 ^ 64)
    (hbb : bPtr.toNat + 4 * (vaId localSize r0 globalOffset localId l).toNat < 2 ^ 64)
    (hboundC : ∀ l', l' < 32 →
      cPtr.toNat + 4 * (vaId localSize r0 globalOffset localId l').toNat < 2 ^ 64)
    (hdistinct : ∀ l', l' < 32 → l' ≠ l →
      cPtr.toNat / 4 + (vaId localSize r0 globalOffset localId l').toNat ≠
        cPtr.toNat / 4 + (vaId localSize r0 globalOffset localId l).toNat) :
    (runVA s (vaPreamble ++ vaTail)).mem
        (cPtr.toNat / 4 + (vaId localSize r0 globalOffset localId l).toNat) =
      s.mem (aPtr.toNat / 4 + (vaId localSize r0 globalOffset localId l).toNat) +
        s.mem (bPtr.toNat / 4 + (vaId localSize r0 globalOffset localId l).toNat) := by
  rw [vaMem s aPtr bPtr cPtr localSize r0 globalOffset localId h]
  have hdistinct' : ∀ l', l' < 32 → l' ≠ l →
      ((fun l' => cPtr + (zext (vaId localSize r0 globalOffset localId l')) <<< 2)
          l').toNat / 4 ≠
        ((fun l' => cPtr + (zext (vaId localSize r0 globalOffset localId l')) <<< 2)
          l).toNat / 4 := by
    intro l' hl' hne
    change vaWord cPtr (vaId localSize r0 globalOffset localId l') ≠
      vaWord cPtr (vaId localSize r0 globalOffset localId l)
    rw [vaWord_eq cPtr (vaId localSize r0 globalOffset localId l') hc (hboundC l' hl'),
      vaWord_eq cPtr (vaId localSize r0 globalOffset localId l) hc (hboundC l hl)]
    exact hdistinct l' hl' hne
  have hword : (BitVec.toNat (cPtr + zext (vaId localSize r0 globalOffset localId l) <<< 2)) / 4 =
      cPtr.toNat / 4 + (vaId localSize r0 globalOffset localId l).toNat := by
    change vaWord cPtr (vaId localSize r0 globalOffset localId l) = _
    rw [vaWord_eq cPtr (vaId localSize r0 globalOffset localId l) hc (hboundC l hl)]
  have hsame := storeVec_same s.mem 32
    (fun l' => cPtr + (zext (vaId localSize r0 globalOffset localId l')) <<< 2)
    (fun l' => low32 ((runVA s (vaPreamble ++ vaTail)).regs 60 l')) l hl hdistinct'
  change storeVec s.mem 32
      (fun l' => cPtr + (zext (vaId localSize r0 globalOffset localId l')) <<< 2)
      (fun l' => low32 ((runVA s (vaPreamble ++ vaTail)).regs 60 l'))
      (BitVec.toNat (cPtr + zext (vaId localSize r0 globalOffset localId l) <<< 2) / 4) =
    low32 ((runVA s (vaPreamble ++ vaTail)).regs 60 l) at hsame
  rw [hword] at hsame
  rw [hsame]
  rw [vaAdd s aPtr bPtr cPtr localSize r0 globalOffset localId h l ha hb hab hbb]
  simp

theorem vaRun_append (s : RealState) (is js : List RInstr) :
    runVA s (is ++ js) = runVA (runVA s is) js :=
  runRealWith_append stepVA s is js

/-- Unrelated words are unchanged by the vector add. -/
theorem vaFrame (s : RealState) (aPtr bPtr cPtr : Addr)
    (localSize r0 globalOffset : Word) (localId : Nat → BitVec 16)
    (h : VaLaunch s aPtr bPtr cPtr localSize r0 globalOffset localId)
    (w : Nat) (hc : cPtr.toNat % 4 = 0)
    (hboundC : ∀ l', l' < 32 →
      cPtr.toNat + 4 * (vaId localSize r0 globalOffset localId l').toNat < 2 ^ 64)
    (hw : ∀ l', l' < 32 →
      w ≠ cPtr.toNat / 4 + (vaId localSize r0 globalOffset localId l').toNat) :
    (runVA s (vaPreamble ++ vaTail)).mem w = s.mem w := by
  rw [vaMem s aPtr bPtr cPtr localSize r0 globalOffset localId h]
  apply storeVec_frame
  intro l' hl'
  change vaWord cPtr (vaId localSize r0 globalOffset localId l') ≠ w
  rw [vaWord_eq cPtr (vaId localSize r0 globalOffset localId l') hc (hboundC l' hl')]
  exact fun he => hw l' hl' he.symm

/-- The real vector add: `c[id] = a[id] + b[id]` at each lane, unrelated words
unchanged, and the kernel halts. -/
theorem realVectorAdd_effect (s : RealState) (aPtr bPtr cPtr : Addr)
    (localSize r0 globalOffset : Word) (localId : Nat → BitVec 16)
    (h : VaLaunch s aPtr bPtr cPtr localSize r0 globalOffset localId)
    (l : Nat) (hl : l < 32) (ha : aPtr.toNat % 4 = 0) (hb : bPtr.toNat % 4 = 0)
    (hc : cPtr.toNat % 4 = 0)
    (hab : aPtr.toNat + 4 * (vaId localSize r0 globalOffset localId l).toNat < 2 ^ 64)
    (hbb : bPtr.toNat + 4 * (vaId localSize r0 globalOffset localId l).toNat < 2 ^ 64)
    (hboundC : ∀ l', l' < 32 →
      cPtr.toNat + 4 * (vaId localSize r0 globalOffset localId l').toNat < 2 ^ 64)
    (hdistinct : ∀ l', l' < 32 → l' ≠ l →
      cPtr.toNat / 4 + (vaId localSize r0 globalOffset localId l').toNat ≠
        cPtr.toNat / 4 + (vaId localSize r0 globalOffset localId l).toNat) :
    (runVA s (vaPreamble ++ vaTail)).halted = true ∧
    (runVA s (vaPreamble ++ vaTail)).mem
        (cPtr.toNat / 4 + (vaId localSize r0 globalOffset localId l).toNat) =
      s.mem (aPtr.toNat / 4 + (vaId localSize r0 globalOffset localId l).toNat) +
        s.mem (bPtr.toNat / 4 + (vaId localSize r0 globalOffset localId l).toNat) ∧
    (∀ w, (∀ l', l' < 32 →
        w ≠ cPtr.toNat / 4 + (vaId localSize r0 globalOffset localId l').toNat) →
      (runVA s (vaPreamble ++ vaTail)).mem w = s.mem w) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [vaRun_append]
    exact vaTail_halted (runVA s vaPreamble)
  · exact vaStore s aPtr bPtr cPtr localSize r0 globalOffset localId h l hl ha hb hc
      hab hbb hboundC hdistinct
  · intro w hw
    exact vaFrame s aPtr bPtr cPtr localSize r0 globalOffset localId h w hc hboundC hw

end

end IntelGpu
