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

end

end IntelGpu
