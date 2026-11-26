-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.RealSemantics
public import Intel.Examples.RealGemm

@[expose] public section

/-!
# A real GEMM's own tables

`RealSemantics` parameterises execution by an alias table and a declared-type
table. This module instantiates both from the real integer GEMM dump:

- `gemmAlias`: the dump's numeric aliases (`V0052 -> V0042`, `V0059 -> V0034`,
  `V0068 -> V0067`, ...).
- `gemmRegType` / `gemmRegElems`: the `.decl` types and element counts.

`gemmPreamble` is the first 11 statements of the decoded program: the label,
the `%cr0` prologue, the two index computations, the `<< 6`, and the two zero
initialisers. `realGemm_preamble_prefix` proves it is a prefix of the decoded
program.

The main results are the loop-entry values:

```lean
gemmI  = localSizeY * r0[6] + zeroExtend(localIdY) + globalOffset[1]
gemmJ0 = localSizeX * r0[1] + zeroExtend(localIdX)
```

`gemmPreamble_entry` states `V0058 = gemmI << 6`, `V0057 = gemmJ0`, and the
zeroed counter and sum at the loop head.
-/

namespace IntelGpu

set_option maxHeartbeats 2000000

noncomputable section

/-- The real GEMM's numeric aliases, from the dump's `.decl` lines. -/
def gemmAlias : Nat → Nat
  | 52 => 42
  | 56 => 41
  | 59 => 34
  | 60 => 35
  | 65 => 63
  | 68 => 67
  | 73 => 71
  | 76 => 75
  | 79 => 61
  | 81 => 36
  | 83 => 80
  | 86 => 85
  | n => n

/-- The real GEMM's declared register types. -/
def gemmRegType : Nat → Option RegType
  | 32 => some .d32
  | 33 => some .d32
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
  | 44 => some .d32
  | 45 => some .d32
  | 46 => some .d32
  | 47 => some .d32
  | 48 => some .d32
  | 49 => some .d32
  | 50 => some .d32
  | 51 => some .d32
  | 52 => some .uw16
  | 53 => some .d32
  | 54 => some .d32
  | 55 => some .d32
  | 56 => some .uw16
  | 57 => some .d32
  | 58 => some .d32
  | 59 => some .q64
  | 60 => some .q64
  | 61 => some .d32
  | 62 => some .d32
  | 63 => some .d32
  | 64 => some .d32
  | 65 => some .ud32
  | 66 => some .q64
  | 67 => some .q64
  | 68 => some .uq64
  | 69 => some .d32
  | 70 => some .d32
  | 71 => some .d32
  | 72 => some .q64
  | 73 => some .ud32
  | 74 => some .q64
  | 75 => some .q64
  | 76 => some .uq64
  | 77 => some .d32
  | 78 => some .d32
  | 79 => some .ud32
  | 80 => some .d32
  | 81 => some .q64
  | 82 => some .q64
  | 83 => some .ud32
  | 84 => some .q64
  | 85 => some .q64
  | 86 => some .uq64
  | _ => none

/-- The real GEMM's declared element counts. -/
def gemmRegElems : Nat → Nat
  | 32 => 16
  | 33 => 16
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
  | 51 => 32
  | 52 => 32
  | 53 => 32
  | 54 => 1
  | 55 => 32
  | 56 => 32
  | 57 => 32
  | 58 => 32
  | 59 => 1
  | 60 => 1
  | 61 => 1
  | 62 => 32
  | 63 => 32
  | 64 => 32
  | 65 => 32
  | 66 => 32
  | 67 => 32
  | 68 => 32
  | 69 => 32
  | 70 => 1
  | 71 => 32
  | 72 => 32
  | 73 => 32
  | 74 => 32
  | 75 => 32
  | 76 => 32
  | 77 => 32
  | 78 => 32
  | 79 => 1
  | 80 => 32
  | 81 => 1
  | 82 => 32
  | 83 => 32
  | 84 => 32
  | 85 => 32
  | 86 => 32
  | _ => 0

def stepGemm : RealState → RInstr → RealState := stepWith gemmAlias gemmRegType

def runGemm (s : RealState) (is : List RInstr) : RealState :=
  runRealWith stepGemm s is

/-- The first 11 statements: label, prologue, index arithmetic, shift, and the
two zero initialisers. -/
def gemmPreamble : List RInstr :=
  [ .label "_main_0",
    .prologue,
    .mul (Exec.nm 1) ⟨50, 0, 0, 1, 1, 0⟩ ⟨40, 0, 1, 0, 1, 0⟩ ⟨38, 0, 6, 0, 1, 0⟩,
    .mov 32 ⟨51, 0, 0, 1, 1, 0⟩ ⟨52, 0, 0, 1, 1, 0⟩,
    .add3 32 ⟨53, 0, 0, 1, 1, 0⟩ ⟨50, 0, 0, 0, 1, 0⟩ ⟨51, 0, 0, 1, 1, 0⟩
      ⟨39, 0, 1, 0, 1, 0⟩,
    .mul (Exec.nm 1) ⟨54, 0, 0, 1, 1, 0⟩ ⟨40, 0, 0, 0, 1, 0⟩ ⟨38, 0, 1, 0, 1, 0⟩,
    .mov 32 ⟨55, 0, 0, 1, 1, 0⟩ ⟨56, 0, 0, 1, 1, 0⟩,
    .add 32 ⟨57, 0, 0, 1, 1, 0⟩ ⟨54, 0, 0, 0, 1, 0⟩ ⟨55, 0, 0, 1, 1, 0⟩,
    .shl 32 ⟨58, 0, 0, 1, 1, 0⟩ ⟨53, 0, 0, 1, 1, 0⟩ 6,
    .movImm (Exec.nm 1) ⟨61, 0, 0, 1, 1, 0⟩ 0 .d32,
    .movImm 32 ⟨62, 0, 0, 1, 1, 0⟩ 0 .d32 ]

theorem realGemm_preamble_prefix :
    (decodeRealProgram realGemm).bind (fun is => is.take 11) = some gemmPreamble := by
  unfold decodeRealProgram decodeRealStmts realGemm gemmPreamble
  decide

/-- The launch facts the GEMM preamble reads. -/
structure GemmLaunch (s : RealState) (aPtr bPtr cPtr : Addr)
    (localSizeX localSizeY r0x r0y goX goY : Word)
    (localIdX localIdY : Nat → BitVec 16) : Prop where
  aReg : s.regs 34 0 = aPtr
  bReg : s.regs 35 0 = bPtr
  cReg : s.regs 36 0 = cPtr
  localSizeXReg : s.regs 40 0 = zext localSizeX
  localSizeYReg : s.regs 40 1 = zext localSizeY
  r0xReg : s.regs 38 1 = zext r0x
  r0yReg : s.regs 38 6 = zext r0y
  localIdXReg : ∀ l, s.regs 41 l = (localIdX l).zeroExtend 64
  localIdYReg : ∀ l, s.regs 42 l = (localIdY l).zeroExtend 64
  goXReg : s.regs 39 0 = zext goX
  goYReg : s.regs 39 1 = zext goY

/-- The row index `i`, from `enqueuedLocalSize[1] * r0[6] + localIdY + globalOffset[1]`. -/
def gemmI (localSizeY r0y : Word) (localIdY : Nat → BitVec 16) (goY : Word)
    (l : Nat) : Word :=
  localSizeY * r0y + (localIdY l).zeroExtend 32 + goY

/-- The column index before the global offset, from
`enqueuedLocalSize[0] * r0[1] + localIdX`. -/
def gemmJ0 (localSizeX r0x : Word) (localIdX : Nat → BitVec 16) (l : Nat) : Word :=
  localSizeX * r0x + (localIdX l).zeroExtend 32

def gemmJ (localSizeX r0x : Word) (localIdX : Nat → BitVec 16) (goX : Word)
    (l : Nat) : Word :=
  gemmJ0 localSizeX r0x localIdX l + goX

theorem gemmPreamble_i (s : RealState) (aPtr bPtr cPtr : Addr)
    (localSizeX localSizeY r0x r0y goX goY : Word)
    (localIdX localIdY : Nat → BitVec 16)
    (h : GemmLaunch s aPtr bPtr cPtr localSizeX localSizeY r0x r0y goX goY
      localIdX localIdY) (l : Nat) :
    (runGemm s gemmPreamble).regs 53 l =
      zext (gemmI localSizeY r0y localIdY goY l) := by
  unfold gemmPreamble runGemm gemmI
  simp [runRealWith, stepGemm, stepWith, writeVecWith, setReg, readRegWith,
    readSrcWith, srcIndex, gemmAlias, isWideOf, gemmRegType, RegType.is64,
    binOpWide, add3Wide, shlWide, h.localSizeYReg, h.r0yReg, h.localIdYReg,
    h.goYReg]

theorem gemmPreamble_j (s : RealState) (aPtr bPtr cPtr : Addr)
    (localSizeX localSizeY r0x r0y goX goY : Word)
    (localIdX localIdY : Nat → BitVec 16)
    (h : GemmLaunch s aPtr bPtr cPtr localSizeX localSizeY r0x r0y goX goY
      localIdX localIdY) (l : Nat) :
    (runGemm s gemmPreamble).regs 57 l =
      zext (gemmJ0 localSizeX r0x localIdX l) := by
  unfold gemmPreamble runGemm gemmJ0
  simp [runRealWith, stepGemm, stepWith, writeVecWith, setReg, readRegWith,
    readSrcWith, srcIndex, gemmAlias, isWideOf, gemmRegType, RegType.is64,
    binOpWide, add3Wide, shlWide, h.localSizeXReg, h.r0xReg, h.localIdXReg]

theorem gemmPreamble_shift (s : RealState) (aPtr bPtr cPtr : Addr)
    (localSizeX localSizeY r0x r0y goX goY : Word)
    (localIdX localIdY : Nat → BitVec 16)
    (h : GemmLaunch s aPtr bPtr cPtr localSizeX localSizeY r0x r0y goX goY
      localIdX localIdY) (l : Nat) :
    (runGemm s gemmPreamble).regs 58 l =
      zext (gemmI localSizeY r0y localIdY goY l <<< 6) := by
  unfold gemmPreamble runGemm gemmI
  simp [runRealWith, stepGemm, stepWith, writeVecWith, setReg, readRegWith,
    readSrcWith, srcIndex, gemmAlias, isWideOf, gemmRegType, RegType.is64,
    binOpWide, add3Wide, shlWide, h.localSizeYReg, h.r0yReg, h.localIdYReg,
    h.goYReg]

theorem gemmPreamble_counter (s : RealState) (aPtr bPtr cPtr : Addr)
    (localSizeX localSizeY r0x r0y goX goY : Word)
    (localIdX localIdY : Nat → BitVec 16)
    (_h : GemmLaunch s aPtr bPtr cPtr localSizeX localSizeY r0x r0y goX goY
      localIdX localIdY) :
    (runGemm s gemmPreamble).regs 61 0 = 0 := by
  unfold gemmPreamble runGemm
  simp [runRealWith, stepGemm, stepWith, writeVecWith, setReg, readRegWith,
    readSrcWith, srcIndex, gemmAlias, isWideOf, gemmRegType, RegType.is64,
    binOpWide, add3Wide, shlWide]

theorem gemmPreamble_sum (s : RealState) (aPtr bPtr cPtr : Addr)
    (localSizeX localSizeY r0x r0y goX goY : Word)
    (localIdX localIdY : Nat → BitVec 16)
    (_h : GemmLaunch s aPtr bPtr cPtr localSizeX localSizeY r0x r0y goX goY
      localIdX localIdY) (l : Nat) :
    (runGemm s gemmPreamble).regs 62 l = 0 := by
  unfold gemmPreamble runGemm
  simp [runRealWith, stepGemm, stepWith, writeVecWith, setReg, readRegWith,
    readSrcWith, srcIndex, gemmAlias, isWideOf, gemmRegType, RegType.is64,
    binOpWide, add3Wide, shlWide]

/-- Every preamble destination has a declared type and matching element count. -/
def RInstr.gemmDstOk : RInstr → Bool
  | .prologue => true
  | .mul n d _ _ => gemmRegElems d.num == n && (gemmRegType d.num).isSome
  | .mov n d _ => gemmRegElems d.num == n && (gemmRegType d.num).isSome
  | .movMasked n d _ => gemmRegElems d.num == n && (gemmRegType d.num).isSome
  | .add3 n d _ _ _ => gemmRegElems d.num == n && (gemmRegType d.num).isSome
  | .shl n d _ _ => gemmRegElems d.num == n && (gemmRegType d.num).isSome
  | .add n d _ _ => gemmRegElems d.num == n && (gemmRegType d.num).isSome
  | .addImm n d _ _ _ => gemmRegElems d.num == n && (gemmRegType d.num).isSome
  | .load n d _ _ => gemmRegElems d == n && (gemmRegType d).isSome
  | .store _ _ _ _ => true
  | .ret _ => true
  | .label _ => true
  | .movImm n d _ _ => gemmRegElems d.num == n && (gemmRegType d.num).isSome
  | .or n d _ _ => gemmRegElems d.num == n && (gemmRegType d.num).isSome
  | .cmpLt _ _ _ _ _ => true
  | .cmpLtReg _ _ _ _ => true
  | .cmpEqReg _ _ _ _ => true
  | .predAnd _ _ _ _ => true
  | .predOr _ _ _ _ => true
  | .goto _ _ => true
  | .gotoIf _ _ _ _ => true
  | .loadScaled n d _ _ _ => gemmRegElems d == n && (gemmRegType d).isSome
  | .storeScaled _ _ _ _ _ => true
  | .sel n _ d _ _ => gemmRegElems d.num == n && (gemmRegType d.num).isSome

theorem gemmPreamble_dst_counts :
    gemmPreamble.all RInstr.gemmDstOk = true := by
  unfold gemmPreamble
  decide

/-- The loop head: `V0058 = i << 6`, `V0057 = j0`, and the zeroed counter and
sum. -/
theorem gemmPreamble_entry (s : RealState) (aPtr bPtr cPtr : Addr)
    (localSizeX localSizeY r0x r0y goX goY : Word)
    (localIdX localIdY : Nat → BitVec 16)
    (h : GemmLaunch s aPtr bPtr cPtr localSizeX localSizeY r0x r0y goX goY
      localIdX localIdY) (l : Nat) :
    (runGemm s gemmPreamble).regs 58 l =
        zext (gemmI localSizeY r0y localIdY goY l <<< 6) ∧
    (runGemm s gemmPreamble).regs 57 l =
        zext (gemmJ0 localSizeX r0x localIdX l) ∧
    (runGemm s gemmPreamble).regs 61 0 = 0 ∧
    (runGemm s gemmPreamble).regs 62 l = 0 :=
  ⟨gemmPreamble_shift s aPtr bPtr cPtr localSizeX localSizeY r0x r0y goX goY
      localIdX localIdY h l,
    gemmPreamble_j s aPtr bPtr cPtr localSizeX localSizeY r0x r0y goX goY
      localIdX localIdY h l,
    gemmPreamble_counter s aPtr bPtr cPtr localSizeX localSizeY r0x r0y goX goY
      localIdX localIdY h,
    gemmPreamble_sum s aPtr bPtr cPtr localSizeX localSizeY r0x r0y goX goY
      localIdX localIdY h l⟩


/-- Bounded `(i <<< 6) ||| k = i * 64 + k`, checked over `Fin 64`. -/
theorem or_shift_six_fin : ∀ a b : Fin 64,
    (BitVec.ofNat 32 a.val <<< 6) ||| BitVec.ofNat 32 b.val =
      BitVec.ofNat 32 a.val * 64 + BitVec.ofNat 32 b.val := by
  decide

theorem or_shift_six (i k : Word) (hi : i.toNat < 64) (hk : k.toNat < 64) :
    (i <<< 6) ||| k = i * 64 + k := by
  have hi' : i = BitVec.ofNat 32 i.toNat := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    omega
  have hk' : k = BitVec.ofNat 32 k.toNat := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    omega
  rw [hi', hk']
  exact or_shift_six_fin ⟨i.toNat, hi⟩ ⟨k.toNat, hk⟩

theorem shl_six (k : Word) : k <<< 6 = k * 64 := by
  bv_omega

theorem or_shift_six_64 (i k : Word) (hi : i.toNat < 64) (hk : k.toNat < 64) :
    (zext (i <<< 6)) ||| (zext k) = zext (i * 64 + k) := by
  show (BitVec.setWidth 64 (i <<< 6)) ||| BitVec.setWidth 64 k =
    BitVec.setWidth 64 (i * 64 + k)
  rw [← BitVec.setWidth_or, or_shift_six i k hi hk]

theorem nat_or_shift_six (i k : Word) (hi : i.toNat < 64) (hk : k.toNat < 64) :
    (i.toNat * 64 % 2 ^ 32 ||| k.toNat) = i.toNat * 64 + k.toNat := by
  have h := congrArg BitVec.toNat (or_shift_six i k hi hk)
  simpa [BitVec.toNat_or, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    BitVec.toNat_add, BitVec.toNat_mul,
    Nat.mod_eq_of_lt (by omega : i.toNat * 64 + k.toNat < 2 ^ 32)] using h

theorem nat_or_shift_six_64 (i k : Word) (hi : i.toNat < 64) (hk : k.toNat < 64) :
    (i.toNat * 64 % 2 ^ 32 % 2 ^ 64 ||| k.toNat % 2 ^ 64) =
      i.toNat * 64 + k.toNat := by
  rw [Nat.mod_eq_of_lt (by omega : i.toNat * 64 % 2 ^ 32 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : k.toNat < 2 ^ 64)]
  exact nat_or_shift_six i k hi hk

/-- Loop-head values: the row shift, the column base, the counter, the sum,
the three pointers and the global X offset. -/
structure GemmLoopInv (s : RealState) (aPtr bPtr cPtr : Addr) (l : Nat)
    (i j0 k sum goX : Word) : Prop where
  v58 : s.regs 58 l = zext (i <<< 6)
  v57 : s.regs 57 l = zext j0
  v61 : s.regs 61 0 = zext k
  v62 : s.regs 62 l = zext sum
  aReg : s.regs 34 0 = aPtr
  bReg : s.regs 35 0 = bPtr
  cReg : s.regs 36 0 = cPtr
  goXReg : s.regs 39 0 = zext goX

/-- The index half of the loop body: `or`, the A byte-address chain, and the
B index chain. -/
def gemmIndexBlock : List RInstr :=
  [ .or 32 ⟨63, 0, 0, 1, 1, 0⟩ ⟨58, 0, 0, 1, 1, 0⟩ ⟨61, 0, 0, 0, 1, 0⟩,
    .mov 32 ⟨64, 0, 0, 1, 1, 0⟩ ⟨65, 0, 0, 1, 1, 0⟩,
    .shl 32 ⟨66, 0, 0, 1, 1, 0⟩ ⟨64, 0, 0, 1, 1, 0⟩ 2,
    .add 32 ⟨67, 0, 0, 1, 1, 0⟩ ⟨66, 0, 0, 1, 1, 0⟩ ⟨59, 0, 0, 0, 1, 0⟩,
    .shl (Exec.nm 1) ⟨70, 0, 0, 1, 1, 0⟩ ⟨61, 0, 0, 0, 1, 0⟩ 6,
    .add3 32 ⟨71, 0, 0, 1, 1, 0⟩ ⟨70, 0, 0, 0, 1, 0⟩ ⟨57, 0, 0, 1, 1, 0⟩
      ⟨39, 0, 0, 0, 1, 0⟩ ]

/-- The A index `i * 64 + k`. -/
theorem gemmIndexA (s : RealState) (aPtr bPtr cPtr : Addr)
    (i j0 k sum goX : Word) (l : Nat)
    (h : GemmLoopInv s aPtr bPtr cPtr l i j0 k sum goX)
    (hi : i.toNat < 64) (hk : k.toNat < 64) :
    (runGemm s gemmIndexBlock).regs 63 l = zext (i * 64 + k) := by
  unfold gemmIndexBlock runGemm
  simp [runRealWith, stepGemm, stepWith, writeVecWith, setReg, readRegWith,
    readSrcWith, srcIndex, gemmAlias, isWideOf, gemmRegType, RegType.is64,
    binOpWide, add3Wide, shlWide, h.v58, h.v61, or_shift_six_64 i k hi hk]

/-- The B index `k * 64 + j0 + globalOffset[0]`. -/
theorem gemmIndexB (s : RealState) (aPtr bPtr cPtr : Addr)
    (i j0 k sum goX : Word) (l : Nat)
    (h : GemmLoopInv s aPtr bPtr cPtr l i j0 k sum goX) :
    (runGemm s gemmIndexBlock).regs 71 l = zext (k * 64 + j0 + goX) := by
  unfold gemmIndexBlock runGemm
  simp [runRealWith, stepGemm, stepWith, writeVecWith, setReg, readRegWith,
    readSrcWith, srcIndex, gemmAlias, isWideOf, gemmRegType, RegType.is64,
    binOpWide, add3Wide, shlWide, h.v57, h.v61, h.goXReg, shl_six]


/-- The `Nat` form of the aligned pointer/index conversion. -/
theorem nat_wordOf_ptr_add_shift (base idx : Nat) (ha : base % 4 = 0)
    (hb : base + 4 * idx < 2 ^ 64) :
    ((idx * 4 + base) % 2 ^ 64) / 4 = base / 4 + idx := by
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- An aligned 64-bit pointer plus a 32-bit word index times four has word
index `base / 4 + idx`, provided the addition does not wrap. -/
theorem wordOf_ptr_add_shift (base : Addr) (idx : Word)
    (hb : base.toNat % 4 = 0)
    (hbound : base.toNat + 4 * idx.toNat < 2 ^ 64) :
    (base + (zext idx) <<< 2).toNat / 4 = base.toNat / 4 + idx.toNat := by
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft]
  have hz : (zext idx).toNat = idx.toNat := by bv_omega
  rw [hz, Nat.shiftLeft_eq]
  omega

/-- The full address half of the loop body: the index block plus the B
move/shift/add. -/
def gemmAddressBlock : List RInstr :=
  gemmIndexBlock ++
    [ .mov 32 ⟨72, 0, 0, 1, 1, 0⟩ ⟨73, 0, 0, 1, 1, 0⟩,
      .shl 32 ⟨74, 0, 0, 1, 1, 0⟩ ⟨72, 0, 0, 1, 1, 0⟩ 2,
      .add 32 ⟨75, 0, 0, 1, 1, 0⟩ ⟨74, 0, 0, 1, 1, 0⟩ ⟨60, 0, 0, 0, 1, 0⟩ ]

/-- The A byte address `V0067`. -/
theorem gemmAddressA (s : RealState) (aPtr bPtr cPtr : Addr)
    (i j0 k sum goX : Word) (l : Nat)
    (h : GemmLoopInv s aPtr bPtr cPtr l i j0 k sum goX)
    (hi : i.toNat < 64) (hk : k.toNat < 64) :
    (runGemm s gemmAddressBlock).regs 67 l =
      (zext (i * 64 + k)) <<< 2 + aPtr := by
  unfold gemmAddressBlock gemmIndexBlock runGemm
  simp [runRealWith, stepGemm, stepWith, writeVecWith, setReg, readRegWith,
    readSrcWith, srcIndex, gemmAlias, isWideOf, gemmRegType, RegType.is64,
    binOpWide, add3Wide, shlWide, h.v58, h.v61, h.aReg, or_shift_six_64 i k hi hk]

/-- The B byte address `V0075`. -/
theorem gemmAddressB (s : RealState) (aPtr bPtr cPtr : Addr)
    (i j0 k sum goX : Word) (l : Nat)
    (h : GemmLoopInv s aPtr bPtr cPtr l i j0 k sum goX) :
    (runGemm s gemmAddressBlock).regs 75 l =
      (zext (k * 64 + j0 + goX)) <<< 2 + bPtr := by
  unfold gemmAddressBlock gemmIndexBlock runGemm
  simp [runRealWith, stepGemm, stepWith, writeVecWith, setReg, readRegWith,
    readSrcWith, srcIndex, gemmAlias, isWideOf, gemmRegType, RegType.is64,
    binOpWide, add3Wide, shlWide, h.v57, h.v61, h.bReg, h.goXReg, shl_six]


/-- The memory and arithmetic half of the loop body: both address chains, both
loads, the multiply and the accumulate. -/
def gemmBodyBlock : List RInstr :=
  [ .or 32 ⟨63, 0, 0, 1, 1, 0⟩ ⟨58, 0, 0, 1, 1, 0⟩ ⟨61, 0, 0, 0, 1, 0⟩,
    .mov 32 ⟨64, 0, 0, 1, 1, 0⟩ ⟨65, 0, 0, 1, 1, 0⟩,
    .shl 32 ⟨66, 0, 0, 1, 1, 0⟩ ⟨64, 0, 0, 1, 1, 0⟩ 2,
    .add 32 ⟨67, 0, 0, 1, 1, 0⟩ ⟨66, 0, 0, 1, 1, 0⟩ ⟨59, 0, 0, 0, 1, 0⟩,
    .load 32 69 .d32 68,
    .shl (Exec.nm 1) ⟨70, 0, 0, 1, 1, 0⟩ ⟨61, 0, 0, 0, 1, 0⟩ 6,
    .add3 32 ⟨71, 0, 0, 1, 1, 0⟩ ⟨70, 0, 0, 0, 1, 0⟩ ⟨57, 0, 0, 1, 1, 0⟩
      ⟨39, 0, 0, 0, 1, 0⟩,
    .mov 32 ⟨72, 0, 0, 1, 1, 0⟩ ⟨73, 0, 0, 1, 1, 0⟩,
    .shl 32 ⟨74, 0, 0, 1, 1, 0⟩ ⟨72, 0, 0, 1, 1, 0⟩ 2,
    .add 32 ⟨75, 0, 0, 1, 1, 0⟩ ⟨74, 0, 0, 1, 1, 0⟩ ⟨60, 0, 0, 0, 1, 0⟩,
    .load 32 77 .d32 76,
    .mul 32 ⟨78, 0, 0, 1, 1, 0⟩ ⟨69, 0, 0, 1, 1, 0⟩ ⟨77, 0, 0, 1, 1, 0⟩,
    .add 32 ⟨62, 0, 0, 1, 1, 0⟩ ⟨62, 0, 0, 1, 1, 0⟩ ⟨78, 0, 0, 1, 1, 0⟩ ]

theorem nat_wordA (aPtr : Addr) (i k : Word) (hi : i.toNat < 64)
    (hk : k.toNat < 64) (ha : aPtr.toNat % 4 = 0)
    (hab : aPtr.toNat + 4 * (i * 64 + k).toNat < 2 ^ 64) :
    (((i.toNat * 64 + k.toNat) * 4 + aPtr.toNat) % 2 ^ 64) / 4 =
      aPtr.toNat / 4 + (i.toNat * 64 + k.toNat) % 2 ^ 32 := by
  have hlt : (i.toNat * 64 + k.toNat) % 2 ^ 32 = i.toNat * 64 + k.toNat := by
    apply Nat.mod_eq_of_lt
    omega
  have htoNat : (i * 64 + k).toNat = i.toNat * 64 + k.toNat := by
    simp [BitVec.toNat_add, BitVec.toNat_mul, hlt]
  have hb : aPtr.toNat + 4 * (i.toNat * 64 + k.toNat) < 2 ^ 64 := by
    rw [← htoNat]
    exact hab
  have h := nat_wordOf_ptr_add_shift aPtr.toNat (i.toNat * 64 + k.toNat) ha hb
  simpa [Nat.shiftLeft_eq, hlt] using h

theorem nat_wordB (bPtr : Addr) (j0 k goX : Word) (hk : k.toNat < 64)
    (hj0 : j0.toNat < 64) (hgoX : goX.toNat < 64) (hb : bPtr.toNat % 4 = 0)
    (hbb : bPtr.toNat + 4 * (k * 64 + j0 + goX).toNat < 2 ^ 64) :
    ((((k.toNat * 64 + j0.toNat + goX.toNat) % 2 ^ 32) * 4 + bPtr.toNat) %
        2 ^ 64) / 4 =
      bPtr.toNat / 4 + (k.toNat * 64 + j0.toNat + goX.toNat) % 2 ^ 32 := by
  have hlt : (k.toNat * 64 + j0.toNat + goX.toNat) % 2 ^ 32 =
      k.toNat * 64 + j0.toNat + goX.toNat := by
    apply Nat.mod_eq_of_lt
    omega
  have htoNat : (k * 64 + j0 + goX).toNat = k.toNat * 64 + j0.toNat + goX.toNat := by
    simp [BitVec.toNat_add, BitVec.toNat_mul, hlt]
  have hbound : bPtr.toNat + 4 * (k.toNat * 64 + j0.toNat + goX.toNat) < 2 ^ 64 := by
    rw [← htoNat]
    exact hbb
  have h := nat_wordOf_ptr_add_shift bPtr.toNat
    (k.toNat * 64 + j0.toNat + goX.toNat) hb hbound
  simpa [Nat.shiftLeft_eq, hlt] using h

theorem gemmWordA (aPtr : Addr) (i k : Word) (hi : i.toNat < 64)
    (hk : k.toNat < 64) (ha : aPtr.toNat % 4 = 0)
    (hab : aPtr.toNat + 4 * (i * 64 + k).toNat < 2 ^ 64) :
    ((((i.toNat * 64 + k.toNat) % 2 ^ 32 % 2 ^ 64) <<< 2 + aPtr.toNat) %
        2 ^ 64) / 4 =
      aPtr.toNat / 4 + (i.toNat * 64 + k.toNat) % 2 ^ 32 := by
  have hlt : (i.toNat * 64 + k.toNat) % 2 ^ 32 = i.toNat * 64 + k.toNat := by
    apply Nat.mod_eq_of_lt
    omega
  have htoNat : (i * 64 + k).toNat = i.toNat * 64 + k.toNat := by
    simp [BitVec.toNat_add, BitVec.toNat_mul, hlt]
  have h2 : (i.toNat * 64 + k.toNat) % 2 ^ 32 % 2 ^ 64 =
      (i.toNat * 64 + k.toNat) % 2 ^ 32 := by
    apply Nat.mod_eq_of_lt
    rw [hlt]
    omega
  rw [h2, Nat.shiftLeft_eq]
  apply nat_wordOf_ptr_add_shift
  · exact ha
  · rw [hlt, ← htoNat]
    exact hab

theorem nat_wordB_mod (bPtr : Addr) (j0 k goX : Word) (hk : k.toNat < 64)
    (hj0 : j0.toNat < 64) (hgoX : goX.toNat < 64) (hb : bPtr.toNat % 4 = 0)
    (hbb : bPtr.toNat + 4 * (k * 64 + j0 + goX).toNat < 2 ^ 64) :
    ((((k.toNat * 64 + j0.toNat % 2 ^ 64 + goX.toNat) % 2 ^ 32) * 4 + bPtr.toNat) %
        2 ^ 64) / 4 =
      bPtr.toNat / 4 + (k.toNat * 64 + j0.toNat + goX.toNat) % 2 ^ 32 := by
  have hj : j0.toNat % 2 ^ 64 = j0.toNat := Nat.mod_eq_of_lt (by omega)
  rw [hj]
  exact nat_wordB bPtr j0 k goX hk hj0 hgoX hb hbb

theorem gemmWordB (bPtr : Addr) (j0 k goX : Word) (hk : k.toNat < 64)
    (hj0 : j0.toNat < 64) (hgoX : goX.toNat < 64) (hb : bPtr.toNat % 4 = 0)
    (hbb : bPtr.toNat + 4 * (k * 64 + j0 + goX).toNat < 2 ^ 64) :
    ((((k.toNat * 64 + j0.toNat % 2 ^ 64 + goX.toNat) % 2 ^ 32 % 2 ^ 64) <<< 2 +
        bPtr.toNat) % 2 ^ 64) / 4 =
      bPtr.toNat / 4 + (k.toNat * 64 + j0.toNat + goX.toNat) % 2 ^ 32 := by
  have hj : j0.toNat % 2 ^ 64 = j0.toNat := Nat.mod_eq_of_lt (by omega)
  rw [hj]
  have hlt : (k.toNat * 64 + j0.toNat + goX.toNat) % 2 ^ 32 =
      k.toNat * 64 + j0.toNat + goX.toNat := by
    apply Nat.mod_eq_of_lt
    omega
  have htoNat : (k * 64 + j0 + goX).toNat = k.toNat * 64 + j0.toNat + goX.toNat := by
    simp [BitVec.toNat_add, BitVec.toNat_mul, hlt]
  have h2 : (k.toNat * 64 + j0.toNat + goX.toNat) % 2 ^ 32 % 2 ^ 64 =
      (k.toNat * 64 + j0.toNat + goX.toNat) % 2 ^ 32 := by
    apply Nat.mod_eq_of_lt
    rw [hlt]
    omega
  rw [h2, Nat.shiftLeft_eq]
  apply nat_wordOf_ptr_add_shift
  · exact hb
  · rw [hlt, ← htoNat]
    exact hbb

theorem gemmLoadA (s : RealState) (aPtr bPtr cPtr : Addr)
    (i j0 k sum goX : Word) (l : Nat)
    (h : GemmLoopInv s aPtr bPtr cPtr l i j0 k sum goX)
    (hi : i.toNat < 64) (hk : k.toNat < 64)
    (ha : aPtr.toNat % 4 = 0)
    (hab : aPtr.toNat + 4 * (i * 64 + k).toNat < 2 ^ 64) :
    (runGemm s gemmBodyBlock).regs 69 l =
      zext (s.mem (aPtr.toNat / 4 + (i * 64 + k).toNat)) := by
  unfold gemmBodyBlock runGemm
  simp [runRealWith, stepGemm, stepWith, writeVecWith, setReg, readRegWith,
    readSrcWith, srcIndex, gemmAlias, isWideOf, gemmRegType, RegType.is64,
    binOpWide, add3Wide, shlWide, load32, h.v58, h.v61, h.aReg,
    nat_or_shift_six_64 i k hi hk, Nat.shiftLeft_eq]
  rw [nat_wordA aPtr i k hi hk ha hab]

theorem gemmLoadB (s : RealState) (aPtr bPtr cPtr : Addr)
    (i j0 k sum goX : Word) (l : Nat)
    (h : GemmLoopInv s aPtr bPtr cPtr l i j0 k sum goX)
    (hk : k.toNat < 64) (hj0 : j0.toNat < 64) (hgoX : goX.toNat < 64)
    (hb : bPtr.toNat % 4 = 0)
    (hbb : bPtr.toNat + 4 * (k * 64 + j0 + goX).toNat < 2 ^ 64) :
    (runGemm s gemmBodyBlock).regs 77 l =
      zext (s.mem (bPtr.toNat / 4 + (k * 64 + j0 + goX).toNat)) := by
  unfold gemmBodyBlock runGemm
  simp [runRealWith, stepGemm, stepWith, writeVecWith, setReg, readRegWith,
    readSrcWith, srcIndex, gemmAlias, isWideOf, gemmRegType, RegType.is64,
    binOpWide, add3Wide, shlWide, load32, h.v57, h.v61, h.bReg, h.goXReg,
    shl_six]
  rw [gemmWordB bPtr j0 k goX hk hj0 hgoX hb hbb]


theorem gemmProduct (s : RealState) (aPtr bPtr cPtr : Addr)
    (i j0 k sum goX : Word) (l : Nat)
    (h : GemmLoopInv s aPtr bPtr cPtr l i j0 k sum goX)
    (hi : i.toNat < 64) (hk : k.toNat < 64) (hj0 : j0.toNat < 64)
    (hgoX : goX.toNat < 64)
    (ha : aPtr.toNat % 4 = 0)
    (hab : aPtr.toNat + 4 * (i * 64 + k).toNat < 2 ^ 64)
    (hb : bPtr.toNat % 4 = 0)
    (hbb : bPtr.toNat + 4 * (k * 64 + j0 + goX).toNat < 2 ^ 64) :
    (runGemm s gemmBodyBlock).regs 78 l =
      zext (s.mem (aPtr.toNat / 4 + (i * 64 + k).toNat) *
        s.mem (bPtr.toNat / 4 + (k * 64 + j0 + goX).toNat)) := by
  unfold gemmBodyBlock runGemm
  simp [runRealWith, stepGemm, stepWith, writeVecWith, setReg, readRegWith,
    readSrcWith, srcIndex, gemmAlias, isWideOf, gemmRegType, RegType.is64,
    binOpWide, add3Wide, shlWide, load32, h.v58, h.v61, h.v57, h.aReg,
    h.bReg, h.goXReg, nat_or_shift_six_64 i k hi hk, shl_six, Nat.shiftLeft_eq]
  rw [nat_wordA aPtr i k hi hk ha hab,
    nat_wordB_mod bPtr j0 k goX hk hj0 hgoX hb hbb]

theorem gemmSum (s : RealState) (aPtr bPtr cPtr : Addr)
    (i j0 k sum goX : Word) (l : Nat)
    (h : GemmLoopInv s aPtr bPtr cPtr l i j0 k sum goX)
    (hi : i.toNat < 64) (hk : k.toNat < 64) (hj0 : j0.toNat < 64)
    (hgoX : goX.toNat < 64)
    (ha : aPtr.toNat % 4 = 0)
    (hab : aPtr.toNat + 4 * (i * 64 + k).toNat < 2 ^ 64)
    (hb : bPtr.toNat % 4 = 0)
    (hbb : bPtr.toNat + 4 * (k * 64 + j0 + goX).toNat < 2 ^ 64) :
    (runGemm s gemmBodyBlock).regs 62 l =
      zext (sum + s.mem (aPtr.toNat / 4 + (i * 64 + k).toNat) *
        s.mem (bPtr.toNat / 4 + (k * 64 + j0 + goX).toNat)) := by
  unfold gemmBodyBlock runGemm
  simp [runRealWith, stepGemm, stepWith, writeVecWith, setReg, readRegWith,
    readSrcWith, srcIndex, gemmAlias, isWideOf, gemmRegType, RegType.is64,
    binOpWide, add3Wide, shlWide, load32, h.v58, h.v61, h.v57, h.v62,
    h.aReg, h.bReg, h.goXReg, nat_or_shift_six_64 i k hi hk, shl_six, Nat.shiftLeft_eq]
  rw [nat_wordA aPtr i k hi hk ha hab,
    nat_wordB_mod bPtr j0 k goX hk hj0 hgoX hb hbb]

/-- One loop-body step: both loaded words, their product, and the new sum. -/
theorem gemmBody (s : RealState) (aPtr bPtr cPtr : Addr)
    (i j0 k sum goX : Word) (l : Nat)
    (h : GemmLoopInv s aPtr bPtr cPtr l i j0 k sum goX)
    (hi : i.toNat < 64) (hk : k.toNat < 64) (hj0 : j0.toNat < 64)
    (hgoX : goX.toNat < 64)
    (ha : aPtr.toNat % 4 = 0)
    (hab : aPtr.toNat + 4 * (i * 64 + k).toNat < 2 ^ 64)
    (hb : bPtr.toNat % 4 = 0)
    (hbb : bPtr.toNat + 4 * (k * 64 + j0 + goX).toNat < 2 ^ 64) :
    (runGemm s gemmBodyBlock).regs 69 l =
        zext (s.mem (aPtr.toNat / 4 + (i * 64 + k).toNat)) ∧
    (runGemm s gemmBodyBlock).regs 77 l =
        zext (s.mem (bPtr.toNat / 4 + (k * 64 + j0 + goX).toNat)) ∧
    (runGemm s gemmBodyBlock).regs 78 l =
        zext (s.mem (aPtr.toNat / 4 + (i * 64 + k).toNat) *
          s.mem (bPtr.toNat / 4 + (k * 64 + j0 + goX).toNat)) ∧
    (runGemm s gemmBodyBlock).regs 62 l =
        zext (sum + s.mem (aPtr.toNat / 4 + (i * 64 + k).toNat) *
          s.mem (bPtr.toNat / 4 + (k * 64 + j0 + goX).toNat)) :=
  ⟨gemmLoadA s aPtr bPtr cPtr i j0 k sum goX l h hi hk ha hab,
    gemmLoadB s aPtr bPtr cPtr i j0 k sum goX l h hk hj0 hgoX hb hbb,
    gemmProduct s aPtr bPtr cPtr i j0 k sum goX l h hi hk hj0 hgoX ha hab hb hbb,
    gemmSum s aPtr bPtr cPtr i j0 k sum goX l h hi hk hj0 hgoX ha hab hb hbb⟩


/-- The loop body plus `cmp.lt` and the counter increment. -/
def gemmBodyStep : List RInstr :=
  gemmBodyBlock ++
    [ .cmpLt (Exec.nm 32) 1 ⟨79, 0, 0, 0, 1, 0⟩ 63 .ud,
      .addImm (Exec.nm 1) ⟨61, 0, 0, 1, 1, 0⟩ ⟨61, 0, 0, 0, 1, 0⟩ 1 .w16 ]

/-- The body block leaves the loop invariants untouched. -/
theorem gemmBodyBlock_frame (s : RealState) (l w p : Nat) :
    (runGemm s gemmBodyBlock).regs 58 l = s.regs 58 l ∧
    (runGemm s gemmBodyBlock).regs 57 l = s.regs 57 l ∧
    (runGemm s gemmBodyBlock).regs 61 l = s.regs 61 l ∧
    (runGemm s gemmBodyBlock).regs 34 l = s.regs 34 l ∧
    (runGemm s gemmBodyBlock).regs 35 l = s.regs 35 l ∧
    (runGemm s gemmBodyBlock).regs 36 l = s.regs 36 l ∧
    (runGemm s gemmBodyBlock).regs 39 l = s.regs 39 l ∧
    (runGemm s gemmBodyBlock).preds p l = s.preds p l ∧
    (runGemm s gemmBodyBlock).mem w = s.mem w := by
  unfold gemmBodyBlock runGemm
  simp [runRealWith, stepGemm, stepWith, writeVecWith, setReg, readRegWith,
    readSrcWith, srcIndex, gemmAlias, isWideOf, gemmRegType, RegType.is64,
    binOpWide, add3Wide, shlWide, load32]


theorem gemmBodyStep_counter (s : RealState) (aPtr bPtr cPtr : Addr)
    (i j0 k sum goX : Word) (l : Nat)
    (h : GemmLoopInv s aPtr bPtr cPtr l i j0 k sum goX) :
    (runGemm s gemmBodyStep).regs 61 0 = zext (k + 1) := by
  unfold gemmBodyStep runGemm
  rw [runRealWith_append]
  simp [runRealWith, gemmBodyBlock, stepGemm, stepWith, writeVecWith, setReg,
    readRegWith, readSrcWith, srcIndex, gemmAlias, isWideOf, gemmRegType,
    RegType.is64, binOpWide, add3Wide, shlWide, addImmWide, load32, h.v61]

theorem gemmBodyStep_pred (s : RealState) (aPtr bPtr cPtr : Addr)
    (i j0 k sum goX : Word) (l : Nat)
    (h : GemmLoopInv s aPtr bPtr cPtr l i j0 k sum goX) (hk : k.toNat < 63) :
    (runGemm s gemmBodyStep).preds 1 0 = true := by
  have h32 : (Exec.nm 32).size = 32 := rfl
  unfold gemmBodyStep runGemm
  rw [runRealWith_append]
  simp [h32, runRealWith, gemmBodyBlock, stepGemm, stepWith, writeVecWith, setReg,
    readRegWith, readSrcWith, srcIndex, gemmAlias, isWideOf, gemmRegType,
    RegType.is64, binOpWide, add3Wide, shlWide, addImmWide, load32, h.v61]
  bv_omega

theorem gemmBodyStep_mem (s : RealState) (aPtr bPtr cPtr : Addr)
    (i j0 k sum goX : Word) (l : Nat)
    (_h : GemmLoopInv s aPtr bPtr cPtr l i j0 k sum goX) :
    (runGemm s gemmBodyStep).mem = s.mem := by
  unfold gemmBodyStep runGemm
  rw [runRealWith_append]
  simp [runRealWith, gemmBodyBlock, stepGemm, stepWith, writeVecWith, setReg,
    readRegWith, readSrcWith, srcIndex, gemmAlias, isWideOf, gemmRegType,
    RegType.is64, binOpWide, add3Wide, shlWide, addImmWide, load32]


theorem gemmBodyStep_sum (s : RealState) (aPtr bPtr cPtr : Addr)
    (i j0 k sum goX : Word) (l : Nat)
    (h : GemmLoopInv s aPtr bPtr cPtr l i j0 k sum goX)
    (hi : i.toNat < 64) (hk : k.toNat < 63) (hj0 : j0.toNat < 64)
    (hgoX : goX.toNat < 64)
    (ha : aPtr.toNat % 4 = 0)
    (hab : aPtr.toNat + 4 * (i * 64 + k).toNat < 2 ^ 64)
    (hb : bPtr.toNat % 4 = 0)
    (hbb : bPtr.toNat + 4 * (k * 64 + j0 + goX).toNat < 2 ^ 64) :
    (runGemm s gemmBodyStep).regs 62 l =
      zext (sum + s.mem (aPtr.toNat / 4 + (i * 64 + k).toNat) *
        s.mem (bPtr.toNat / 4 + (k * 64 + j0 + goX).toNat)) := by
  have hk64 : k.toNat < 64 := by omega
  have hj64 : j0.toNat % 2 ^ 64 = j0.toNat := Nat.mod_eq_of_lt (by omega)
  unfold gemmBodyStep runGemm
  rw [runRealWith_append]
  simp [runRealWith, gemmBodyBlock, stepGemm, stepWith, writeVecWith, setReg,
    readRegWith, readSrcWith, srcIndex, gemmAlias, isWideOf, gemmRegType,
    RegType.is64, binOpWide, add3Wide, shlWide, addImmWide, load32,
    h.v58, h.v61, h.v57, h.v62, h.aReg, h.bReg, h.goXReg,
    nat_or_shift_six_64 i k hi hk64, shl_six, hj64, Nat.shiftLeft_eq]
  rw [nat_wordA aPtr i k hi hk64 ha hab,
    nat_wordB bPtr j0 k goX hk64 hj0 hgoX hb hbb]

theorem gemmBodyStep_frame (s : RealState) (l w : Nat) :
    (runGemm s gemmBodyStep).regs 58 l = s.regs 58 l ∧
    (runGemm s gemmBodyStep).regs 57 l = s.regs 57 l ∧
    (runGemm s gemmBodyStep).regs 34 l = s.regs 34 l ∧
    (runGemm s gemmBodyStep).regs 35 l = s.regs 35 l ∧
    (runGemm s gemmBodyStep).regs 36 l = s.regs 36 l ∧
    (runGemm s gemmBodyStep).regs 39 l = s.regs 39 l ∧
    (runGemm s gemmBodyStep).mem w = s.mem w := by
  unfold gemmBodyStep runGemm
  rw [runRealWith_append]
  simp [runRealWith, gemmBodyBlock, stepGemm, stepWith, writeVecWith, setReg,
    readRegWith, readSrcWith, srcIndex, gemmAlias, isWideOf, gemmRegType,
    RegType.is64, binOpWide, add3Wide, shlWide, addImmWide, load32]


/-- One real loop iteration: the invariant advances to `k + 1`, the sum gains
`mem A * mem B`, and `P1 = k < 63` is true. -/
theorem gemmBodyStep_inv (s : RealState) (aPtr bPtr cPtr : Addr)
    (i j0 k sum goX : Word) (l : Nat)
    (h : GemmLoopInv s aPtr bPtr cPtr l i j0 k sum goX)
    (hi : i.toNat < 64) (hk : k.toNat < 63) (hj0 : j0.toNat < 64)
    (hgoX : goX.toNat < 64)
    (ha : aPtr.toNat % 4 = 0)
    (hab : aPtr.toNat + 4 * (i * 64 + k).toNat < 2 ^ 64)
    (hb : bPtr.toNat % 4 = 0)
    (hbb : bPtr.toNat + 4 * (k * 64 + j0 + goX).toNat < 2 ^ 64) :
    GemmLoopInv (runGemm s gemmBodyStep) aPtr bPtr cPtr l i j0 (k + 1)
        (sum + s.mem (aPtr.toNat / 4 + (i * 64 + k).toNat) *
          s.mem (bPtr.toNat / 4 + (k * 64 + j0 + goX).toNat)) goX ∧
    (runGemm s gemmBodyStep).preds 1 0 = true ∧
    (runGemm s gemmBodyStep).mem = s.mem := by
  have hf0 := gemmBodyStep_frame s 0 0
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    gemmBodyStep_pred s aPtr bPtr cPtr i j0 k sum goX l h hk,
    gemmBodyStep_mem s aPtr bPtr cPtr i j0 k sum goX l h⟩
  · exact (gemmBodyStep_frame s l 0).1.trans h.v58
  · exact (gemmBodyStep_frame s l 0).2.1.trans h.v57
  · exact gemmBodyStep_counter s aPtr bPtr cPtr i j0 k sum goX l h
  · exact gemmBodyStep_sum s aPtr bPtr cPtr i j0 k sum goX l h hi hk hj0 hgoX
      ha hab hb hbb
  · exact hf0.2.2.1.trans h.aReg
  · exact hf0.2.2.2.1.trans h.bReg
  · exact hf0.2.2.2.2.1.trans h.cReg
  · exact hf0.2.2.2.2.2.1.trans h.goXReg

/-- The epilogue: C index, byte address, store and return. -/
def gemmEpilogue : List RInstr :=
  [ .add3 32 ⟨80, 0, 0, 1, 1, 0⟩ ⟨58, 0, 0, 1, 1, 0⟩ ⟨57, 0, 0, 1, 1, 0⟩
      ⟨39, 0, 0, 0, 1, 0⟩,
    .mov 32 ⟨82, 0, 0, 1, 1, 0⟩ ⟨83, 0, 0, 1, 1, 0⟩,
    .shl 32 ⟨84, 0, 0, 1, 1, 0⟩ ⟨82, 0, 0, 1, 1, 0⟩ 2,
    .add 32 ⟨85, 0, 0, 1, 1, 0⟩ ⟨84, 0, 0, 1, 1, 0⟩ ⟨81, 0, 0, 0, 1, 0⟩,
    .store 32 86 .d32 62,
    .ret 1 ]

/-- The C byte address `V0085`. -/
theorem gemmEpilogue_address (s : RealState) (aPtr bPtr cPtr : Addr)
    (i j0 k sum goX : Word) (l : Nat)
    (h : GemmLoopInv s aPtr bPtr cPtr l i j0 k sum goX) :
    (runGemm s gemmEpilogue).regs 85 l =
      (zext (i * 64 + j0 + goX)) <<< 2 + cPtr := by
  unfold gemmEpilogue runGemm
  simp [runRealWith, stepGemm, stepWith, writeVecWith, setReg, readRegWith,
    readSrcWith, srcIndex, gemmAlias, isWideOf, gemmRegType, RegType.is64,
    binOpWide, add3Wide, shlWide, h.v58, h.v57, h.cReg, h.goXReg, shl_six]

end

end IntelGpu
