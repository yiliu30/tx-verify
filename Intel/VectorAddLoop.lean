-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.RealSemantics
public import Intel.Examples.RealVectorAdd

@[expose] public section

/-!
# The real loop vector add: tables and the index preamble

`Intel/Examples/RealVectorAdd.lean` is the exact IGC dump for the
`RoundedRangeKernel` vector add. This module transcribes its `.decl` aliases
and types and proves the first per-lane index computation.

The source IR is `while (id < N) { c[id] = a[id] + b[id]; id += N; }` with a
32-lane work-group. Stage 103 fixed destination `<hstride>` parsing; this module
uses the corrected regions.
-/

namespace IntelGpu

noncomputable section

/-- The loop vector add's numeric aliases, from the dump's `.decl` lines. -/
def vaLoopAlias : Nat → Nat
  | 50 => 45
  | 52 => 38
  | 53 => 35
  | 55 => 39
  | 58 => 36
  | 61 => 59
  | 64 => 62
  | 65 => 49
  | 66 => 63
  | 68 => 37
  | 74 => 72
  | 77 => 75
  | 78 => 76
  | 81 => 59
  | 82 => 79
  | 83 => 80
  | n => n

/-- The loop vector add's declared register types. -/
def vaLoopRegType : Nat → Option RegType
  | 35 => some .d32
  | 36 => some .d32
  | 37 => some .d32
  | 38 => some .d32
  | 39 => some .w16
  | 45 => some .q64
  | 46 => some .q64
  | 47 => some .q64
  | 48 => some .q64
  | 49 => some .d32
  | 51 => some .q64
  | 54 => some .q64
  | 56 => some .q64
  | 57 => some .q64
  | 59 => some .q64
  | 62 => some .d32
  | 63 => some .d32
  | 67 => some .q64
  | 69 => some .d32
  | 70 => some .d32
  | 71 => some .d32
  | 72 => some .q64
  | 75 => some .d32
  | 76 => some .d32
  | 79 => some .d32
  | 80 => some .d32
  | _ => none

/-- Declared element counts for the registers this module writes. -/
def vaLoopRegElems : Nat → Nat
  | 35 => 8
  | 36 => 3
  | 37 => 3
  | 38 => 3
  | 39 => 32
  | 45 => 1
  | 46 => 1
  | 47 => 1
  | 48 => 1
  | 49 => 2
  | 51 => 1
  | 54 => 32
  | 56 => 32
  | 57 => 1
  | 59 => 32
  | 62 => 32
  | 63 => 32
  | 65 => 2
  | 67 => 1
  | 69 => 32
  | 70 => 32
  | 71 => 32
  | 72 => 32
  | 74 => 64
  | 75 => 32
  | 76 => 32
  | 79 => 32
  | 80 => 32
  | 81 => 64
  | 82 => 32
  | 83 => 32
  | _ => 0

def stepVAL : RealState → RInstr → RealState := stepWith vaLoopAlias vaLoopRegType

def runVAL (s : RealState) (is : List RInstr) : RealState := runRealWith stepVAL s is

/-- The first eight statements: label, prologue and the six index operations. -/
def vaLoopPreamble : List RInstr :=
  [ .label "_main_0",
    .prologue,
    .mov (Exec.nm 2) ⟨49, 0, 0, 1, 1, 1⟩ ⟨50, 0, 0, 1, 1, 0⟩,
    .mul (Exec.nm 1) ⟨51, 0, 0, 1, 1, 1⟩ ⟨52, 0, 0, 0, 1, 0⟩
      ⟨53, 0, 1, 0, 1, 0⟩,
    .mov 32 ⟨54, 0, 0, 1, 1, 1⟩ ⟨55, 0, 0, 1, 1, 0⟩,
    .add 32 ⟨56, 0, 0, 1, 1, 1⟩ ⟨51, 0, 0, 0, 1, 0⟩ ⟨54, 0, 0, 1, 1, 0⟩,
    .mov (Exec.nm 1) ⟨57, 0, 0, 1, 1, 1⟩ ⟨58, 0, 0, 0, 1, 0⟩,
    .add 32 ⟨59, 0, 0, 1, 1, 1⟩ ⟨56, 0, 0, 1, 1, 0⟩ ⟨57, 0, 0, 0, 1, 0⟩ ]

theorem realVectorAdd_preamble_prefix :
    (decodeRealProgram realVectorAdd).bind (fun is => is.take 8) = some vaLoopPreamble := by
  unfold decodeRealProgram decodeRealStmts realVectorAdd vaLoopPreamble
  decide

/-- Launch facts used by the index preamble. -/
structure VaLoopLaunch (s : RealState) (localSize r0 globalOffset : Word)
    (localId : Nat → BitVec 16) : Prop where
  localSizeReg : s.regs 38 0 = zext localSize
  r0Reg : s.regs 35 1 = zext r0
  localIdReg : ∀ l, s.regs 39 l = (localId l).zeroExtend 64
  offsetReg : s.regs 36 0 = zext globalOffset

/-- The per-lane 64-bit ID computed by the preamble. -/
def vaLoopId (localSize r0 globalOffset : Word) (localId : Nat → BitVec 16)
    (l : Nat) : Addr :=
  zext localSize * zext r0 + (localId l).zeroExtend 64 + zext globalOffset

theorem vaLoopPreamble_id (s : RealState) (localSize r0 globalOffset : Word)
    (localId : Nat → BitVec 16) (l : Nat)
    (h : VaLoopLaunch s localSize r0 globalOffset localId) :
    (runVAL s vaLoopPreamble).regs 59 l =
      vaLoopId localSize r0 globalOffset localId l := by
  unfold vaLoopPreamble runVAL stepVAL
  simp [runRealWith, stepWith, writeVecWith, setReg, readRegWith, readSrcWith,
    srcIndex, vaLoopAlias, vaLoopRegType, isWideOf, RegType.is64, binOpWide,
    h.localSizeReg, h.r0Reg, h.localIdReg, h.offsetReg, vaLoopId]

/-- The index preamble changes registers only. -/
theorem vaLoopPreamble_mem (s : RealState) :
    (runVAL s vaLoopPreamble).mem = s.mem := by
  unfold vaLoopPreamble runVAL stepVAL
  simp [runRealWith, stepWith, writeVecWith]

end

end IntelGpu
