-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.RealDecode
public import Intel.AddOne

@[expose] public section

/-!
# Executing the decoded real kernel

Stage 63 decoded the real IGC add-one kernel. This module gives those decoded
instructions a semantics with the two features the kernel needs beyond the
scalar core: register regions and register aliases.

## Registers, regions, aliases

Each register element is a 64-bit slot. A `d32` operation truncates its result
to 32 bits and zero-extends into the slot; a `q` operation uses all 64 bits. The
choice is made by the destination's declared type, transcribed from the dump's
`.decl` lines into `regType`.

`srcIndex` interprets a source region:

- `(0,0)<0;1,0>` broadcasts element 0, and `(0,1)<0;1,0>` element 1;
- `(0,0)<1>` and `(0,0)<1;1,0>` are dense: lane `l` reads element `l`.

Every region in this kernel has width 1 and horizontal stride 0, and every
destination starts at `(0,0)`; `realAddOne_regions_simple` checks that on the
decoded program, so the interpretation is not a silent guess.

The `or` prologue is a no-op here: it writes `%cr0`, which no later
instruction reads.

Aliases are the dump's: `V0053` aliases `V0052` (the computed address),
`V0049` aliases `V0047`, `V0050` aliases `V0034`, and `V0046` aliases `V0039`.
`V0033` and `V0036` alias `%r0`, which the kernel only reads, so they stay
independent inputs here.

## Predicates and control flow

`RealState.preds` is indexed by predicate and lane: `cmp.lt` writes the
per-lane comparison on active lanes, and `gotoIf` reads lane 0 because the
modeled branch is uniform. `runRealCF` interprets labels, `goto` and
`gotoIf` with fuel, so a branch target outside the program stops the run. The
add-one proofs keep using the straight-line `runReal`; label resolution for the
real GEMM is proved in `Intel.RealGemmCoverage`.

## What is proved

- `realAddOne_decoded_eq`: the decoder's output is the instruction list below.
- `realAddOne_address_preamble`: at every lane index (the model is total;
  the effect theorem restricts to the 32-lane launch), `V0053` holds
  `base + (zeroExtend (localSize * r0[1] + zeroExtend(localId[l]) + globalOffset)) <<< 2`,
  matching the source IR's `%12 = (%9 << 2) + %10`.
- `realAddOne_effect`: running the program halts, gives every active lane an
  aligned address, increments the word originally at that address, and
  preserves every other word, under a distinct-address hypothesis. Distinct
  word addresses are the race-freedom hypothesis; the load, the add and the
  store are the only memory operations.
-/

namespace IntelGpu

noncomputable section

/-- Declared register types, as printed by the dump's `.decl` lines. -/
inductive RegType where
  | d32
  | ud32
  | w16
  | uw16
  | q64
  | uq64
  deriving Repr, DecidableEq

def RegType.is64 : RegType → Bool
  | .q64 | .uq64 => true
  | _ => false

/-- Types of the registers this kernel touches, from the dump's `.decl` table. -/
def regType : Nat → Option RegType
  | 34 => some .uq64
  | 36 => some .d32
  | 37 => some .d32
  | 38 => some .d32
  | 39 => some .w16
  | 44 => some .d32
  | 45 => some .d32
  | 46 => some .uw16
  | 47 => some .d32
  | 48 => some .q64
  | 49 => some .ud32
  | 50 => some .q64
  | 51 => some .q64
  | 52 => some .q64
  | 53 => some .uq64
  | 54 => some .d32
  | 55 => some .d32
  | _ => none

def isWideOf (typeOf : Nat → Option RegType) (r : Nat) : Bool :=
  match typeOf r with
  | some t => t.is64
  | none => false

abbrev isWide (r : Nat) : Bool := isWideOf regType r

/-- A register file with 64-bit slots, word-addressed global memory and a halt
flag. -/
structure RealState where
  regs : Nat → Nat → Addr
  /-- Predicate registers, one bit per predicate and lane. `cmp.lt` writes
  the per-lane comparison; the GEMM's uniform branch reads lane 0. -/
  preds : Nat → Nat → Bool
  mem : Nat → Word
  halted : Bool

/-- The numeric aliases in the dump, for registers this kernel reads or writes.
`%r0` aliases are inputs and are not modelled as numeric registers. -/
def aliasBase : Nat → Nat
  | 46 => 39
  | 49 => 47
  | 50 => 34
  | 53 => 52
  | n => n

def readRegWith (alias : Nat → Nat) (s : RealState) (r e : Nat) : Addr :=
  s.regs (alias r) e

/-- A scalar register (one declared element) reads element zero. -/
def readScalarWith (alias : Nat → Nat) (s : RealState) (r : Nat) : Addr :=
  s.regs (alias r) 0

abbrev readReg (s : RealState) (r e : Nat) : Addr := readRegWith aliasBase s r e

/-- Element index selected by a source region at lane `l`. All regions here
have width 1 and horizontal stride 0, so only the vertical stride decides
between a broadcast and a dense read. -/
def srcIndex (g : Grf) (l : Nat) : Nat :=
  g.row * 8 + g.col + if g.vstride = 0 then 0 else l

def readSrcWith (alias : Nat → Nat) (s : RealState) (g : Grf) (l : Nat) : Addr :=
  readRegWith alias s g.num (srcIndex g l)

abbrev readSrc (s : RealState) (g : Grf) (l : Nat) : Addr := readSrcWith aliasBase s g l

/-- Destination element index for region element `i`. -/
def Grf.dstIndex (g : Grf) (i : Nat) : Nat :=
  g.row * 8 + g.col + i * g.hstride

/-- Full source-region index for region element `i`, including vertical and
horizontal stride. -/
def srcIndexRegion (g : Grf) (i : Nat) : Nat :=
  g.row * 8 + g.col +
    (i / g.width) * g.vstride + (i % g.width) * g.hstride

def readSrcIndexed (alias : Nat → Nat) (s : RealState) (g : Grf) (i : Nat) : Addr :=
  readRegWith alias s g.num (srcIndexRegion g i)

/-- A mask-enabled hardware lane. -/
def Exec.laneActive (e : Exec) (l : Nat) : Bool :=
  if e.noMask then decide (l < e.size)
  else decide (e.offset ≤ l ∧ l < e.offset + e.size)

/-- The operand element index for a mask-enabled hardware lane. -/
def Exec.laneIndex (e : Exec) (l : Nat) : Nat :=
  if e.noMask then l else l - e.offset

def setReg (regs : Nat → Nat → Addr) (r : Nat) (g : Nat → Addr) : Nat → Nat → Addr :=
  fun r' e => if r' = r then g e else regs r' e

/-- Write all declared elements of a destination register. This is exact for
this kernel: every destination's `.decl` element count equals its execution
size, checked by `realAddOne_dst_counts`. -/
def writeVecWith (alias : Nat → Nat) (s : RealState) (r : Nat)
    (f : Nat → Addr) : RealState :=
  { s with regs := setReg s.regs (alias r) f }

abbrev writeVec (s : RealState) (r : Nat) (f : Nat → Addr) : RealState :=
  writeVecWith aliasBase s r f

/-- Write a destination region only on task-active lanes. Unit and stride-two
destinations are enough for the real vector add; other strides are preserved
rather than guessed at. -/
def writeMaskedWith (alias : Nat → Nat) (s : RealState) (dst : Grf) (e : Exec)
    (f : Nat → Addr) : RealState :=
  { s with regs := fun r j =>
      if r = alias dst.num then
        let base := dst.row * 8 + dst.col
        let k := j - base
        if dst.hstride = 1 ∧ base ≤ j then
          let i := k
          let l := if e.noMask then i else e.offset + i
          if e.laneActive l then f i else s.regs r j
        else if dst.hstride = 2 ∧ base ≤ j ∧ k % 2 = 0 then
          let i := k / 2
          let l := if e.noMask then i else e.offset + i
          if e.laneActive l then f i else s.regs r j
        else s.regs r j
      else s.regs r j }

@[simp] theorem writeVecWith_same (alias : Nat → Nat) (s : RealState) (r : Nat)
    (f : Nat → Addr) (e : Nat) :
    (writeVecWith alias s r f).regs (alias r) e = f e := by
  simp [writeVecWith, setReg]

@[simp] theorem writeVecWith_ne (alias : Nat → Nat) (s : RealState) (r : Nat)
    (f : Nat → Addr) (r' e : Nat) (h : alias r' ≠ alias r) :
    (writeVecWith alias s r f).regs (alias r') e = s.regs (alias r') e := by
  simp [writeVecWith, setReg, h]

abbrev low32 (a : Addr) : Word := a.truncate 32

abbrev zext (w : Word) : Addr := w.zeroExtend 64

@[simp] theorem low32_zext (w : Word) : low32 (zext w) = w := by
  bv_omega

@[simp] theorem low32_zext16 (w : BitVec 16) :
    low32 (w.zeroExtend 64) = w.zeroExtend 32 := by
  bv_omega

def binOpWide (wide : Bool) (f32 : Word → Word → Word)
    (f64 : Addr → Addr → Addr) (x y : Addr) : Addr :=
  if wide then f64 x y else zext (f32 (low32 x) (low32 y))

abbrev binOp (dst : Nat) (f32 : Word → Word → Word) (f64 : Addr → Addr → Addr)
    (x y : Addr) : Addr := binOpWide (isWide dst) f32 f64 x y

def add3Wide (wide : Bool) (x y z : Addr) : Addr :=
  if wide then x + y + z else zext (low32 x + low32 y + low32 z)

abbrev add3Op (dst : Nat) (x y z : Addr) : Addr := add3Wide (isWide dst) x y z

def shlWide (wide : Bool) (x : Addr) (k : Nat) : Addr :=
  if wide then x <<< k else zext (low32 x <<< k)

abbrev shlOp (dst : Nat) (x : Addr) (k : Nat) : Addr := shlWide (isWide dst) x k

def addImmWide (wide : Bool) (x : Addr) (imm : Word) : Addr :=
  if wide then x + zext imm else zext (low32 x + imm)

abbrev addImmOp (dst : Nat) (x : Addr) (imm : Word) : Addr :=
  addImmWide (isWide dst) x imm

/-- A vector store: word `w` receives the value of some active lane whose
address is `w`. Distinct addresses make that lane unique, which is what
`storeVec_same` uses; without them the choice is an arbitrary racing lane. -/
def storeVec (m : Nat → Word) (n : Nat) (addr : Nat → Addr)
    (val : Nat → Word) : Nat → Word :=
  fun w =>
    if h : ∃ l, l < n ∧ (addr l).toNat / 4 = w then val (Classical.choose h) else m w

theorem storeVec_same (m : Nat → Word) (n : Nat) (addr : Nat → Addr)
    (val : Nat → Word) (l : Nat) (hl : l < n)
    (hdistinct : ∀ k, k < n → k ≠ l → (addr k).toNat / 4 ≠ (addr l).toNat / 4) :
    storeVec m n addr val ((addr l).toNat / 4) = val l := by
  unfold storeVec
  have hex : ∃ k, k < n ∧ (addr k).toNat / 4 = (addr l).toNat / 4 := ⟨l, hl, rfl⟩
  rw [dite_eq_left hex]
  have hchoose : Classical.choose hex = l := by
    rcases Classical.choose_spec hex with ⟨hk, he⟩
    by_cases h : Classical.choose hex = l
    · exact h
    · exact absurd he (hdistinct _ hk h)
  rw [hchoose]

theorem storeVec_frame (m : Nat → Word) (n : Nat) (addr : Nat → Addr)
    (val : Nat → Word) (w : Nat)
    (h : ∀ l, l < n → (addr l).toNat / 4 ≠ w) :
    storeVec m n addr val w = m w := by
  unfold storeVec
  have hnot : ¬ ∃ l, l < n ∧ (addr l).toNat / 4 = w := by
    intro hex
    exact h hex.choose hex.choose_spec.1 hex.choose_spec.2
  rw [dite_eq_right hnot]

def stepWith (alias : Nat → Nat) (typeOf : Nat → Option RegType) :
    RealState → RInstr → RealState
  | s, .prologue => s
  | s, .mul _ dst a b =>
      writeVecWith alias s dst.num (fun l =>
        binOpWide (isWideOf typeOf dst.num) (fun x y => x * y) (fun x y => x * y)
          (readSrcWith alias s a l) (readSrcWith alias s b l))
  | s, .mov _ dst src =>
      writeVecWith alias s dst.num (fun l => readSrcWith alias s src l)
  | s, .movMasked e dst src =>
      writeMaskedWith alias s dst e (fun i => readSrcIndexed alias s src i)
  | s, .add3 _ dst a b c =>
      writeVecWith alias s dst.num (fun l =>
        add3Wide (isWideOf typeOf dst.num) (readSrcWith alias s a l)
          (readSrcWith alias s b l) (readSrcWith alias s c l))
  | s, .shl _ dst src k =>
      writeVecWith alias s dst.num (fun l =>
        shlWide (isWideOf typeOf dst.num) (readSrcWith alias s src l) k)
  | s, .add _ dst a b =>
      writeVecWith alias s dst.num (fun l =>
        binOpWide (isWideOf typeOf dst.num) (fun x y => x + y) (fun x y => x + y)
          (readSrcWith alias s a l) (readSrcWith alias s b l))
  | s, .addImm _ dst src imm _ =>
      writeVecWith alias s dst.num (fun l =>
        addImmWide (isWideOf typeOf dst.num) (readSrcWith alias s src l)
          (BitVec.ofNat 32 imm))
  | s, .load _ dst _ addrReg =>
      writeVecWith alias s dst (fun l =>
        zext (load32 s.mem (readRegWith alias s addrReg l).toNat))
  | s, .store n addrReg _ src =>
      { s with
        mem := storeVec s.mem n (fun l => readRegWith alias s addrReg l)
          (fun l => low32 (readRegWith alias s src l)) }
  | s, .loadScaled _ dst _ base idx =>
      writeVecWith alias s dst (fun l =>
        zext (load32 s.mem
          (readScalarWith alias s base + ((readRegWith alias s idx l) <<< 2)).toNat))
  | s, .storeScaled n base idx _ src =>
      { s with
        mem := storeVec s.mem n
          (fun l => readScalarWith alias s base + ((readRegWith alias s idx l) <<< 2))
          (fun l => low32 (readRegWith alias s src l)) }
  | s, .sel _ p dst a b =>
      writeVecWith alias s dst.num (fun l =>
        if s.preds p l then readSrcWith alias s a l else readSrcWith alias s b l)
  | s, .ret _ => { s with halted := true }
  | s, .label _ => s
  | s, .movImm _ dst imm _ =>
      writeVecWith alias s dst.num (fun _ => zext (BitVec.ofNat 32 imm))
  | s, .or _ dst a b =>
      writeVecWith alias s dst.num (fun l =>
        binOpWide (isWideOf typeOf dst.num) (fun x y => x ||| y) (fun x y => x ||| y)
          (readSrcWith alias s a l) (readSrcWith alias s b l))
  | s, .cmpLt n p src imm _ =>
      { s with
        preds := fun p' l =>
          if p' = p ∧ l < n then
            decide (low32 (readSrcWith alias s src l) < BitVec.ofNat 32 imm)
          else s.preds p' l }
  | s, .cmpLtReg n p a b =>
      { s with
        preds := fun p' l =>
          if p' = p ∧ l < n then
            decide (low32 (readSrcWith alias s a l) < low32 (readSrcWith alias s b l))
          else s.preds p' l }
  | s, .cmpEqReg n p a b =>
      { s with
        preds := fun p' l =>
          if p' = p ∧ l < n then
            decide (low32 (readSrcWith alias s a l) = low32 (readSrcWith alias s b l))
          else s.preds p' l }
  | s, .predAnd n p a b =>
      { s with
        preds := fun p' l =>
          if p' = p ∧ l < n then s.preds a l && s.preds b l else s.preds p' l }
  | s, .predOr n p a b =>
      { s with
        preds := fun p' l =>
          if p' = p ∧ l < n then s.preds a l || s.preds b l else s.preds p' l }
  | s, .goto _ _ => s
  | s, .gotoIf _ _ _ _ => s

/-- The add-one instance of `stepWith`. -/
abbrev stepReal : RealState → RInstr → RealState := stepWith aliasBase regType

/-- The straight-line fold. -/
def runRealWith (step : RealState → RInstr → RealState) (s : RealState)
    (is : List RInstr) : RealState := is.foldl step s

/-- The add-one instance; control flow is interpreted by `runRealCF`. -/
abbrev runReal (s : RealState) (is : List RInstr) : RealState :=
  runRealWith stepReal s is

/-- Find a label's program counter. -/
def labelIndexGo : List RInstr → String → Nat → Option Nat
  | [], _, _ => none
  | .label n :: rest, name, i =>
      if n = name then some i else labelIndexGo rest name (i + 1)
  | _ :: rest, name, i => labelIndexGo rest name (i + 1)

def labelIndex (code : List RInstr) (name : String) : Option Nat :=
  labelIndexGo code name 0

/-- A fuel-based control-flow interpreter. `goto` targets are labels in the
same list, `gotoIf` reads a uniform predicate, and fuel makes termination
structural. -/
def runRealCFWith (step : RealState → RInstr → RealState) (code : List RInstr)
    (s : RealState) (pc fuel : Nat) : RealState :=
  match fuel with
  | 0 => s
  | fuel + 1 =>
      match code[pc]? with
      | none => s
      | some (.label _) => runRealCFWith step code s (pc + 1) fuel
      | some (.goto _ l) =>
          match labelIndex code l with
          | some pc' => runRealCFWith step code s pc' fuel
          | none => s
      | some (.gotoIf _ p negated l) =>
          let taken := if negated then !(s.preds p 0) else s.preds p 0
          if taken then
            match labelIndex code l with
            | some pc' => runRealCFWith step code s pc' fuel
            | none => s
          else runRealCFWith step code s (pc + 1) fuel
      | some i => runRealCFWith step code (step s i) (pc + 1) fuel

/-- The add-one instance of the control-flow interpreter. -/
abbrev runRealCF := runRealCFWith stepReal

theorem runRealWith_append (step : RealState → RInstr → RealState)
    (s : RealState) (is js : List RInstr) :
    runRealWith step s (is ++ js) = runRealWith step (runRealWith step s is) js := by
  simp [runRealWith, List.foldl_append]

theorem runReal_append (s : RealState) (is js : List RInstr) :
    runReal s (is ++ js) = runReal (runReal s is) js :=
  runRealWith_append stepReal s is js

/-- The address computation, as decoded: mul, two moves, add3, shift and add. -/
def realAddOnePreamble : List RInstr :=
  [ .prologue,
    .mul (Exec.nm 1) ⟨44, 0, 0, 1, 1, 0⟩ ⟨38, 0, 0, 0, 1, 0⟩ ⟨36, 0, 1, 0, 1, 0⟩,
    .mov 32 ⟨45, 0, 0, 1, 1, 0⟩ ⟨46, 0, 0, 1, 1, 0⟩,
    .add3 32 ⟨47, 0, 0, 1, 1, 0⟩ ⟨44, 0, 0, 0, 1, 0⟩ ⟨45, 0, 0, 1, 1, 0⟩
      ⟨37, 0, 0, 0, 1, 0⟩,
    .mov 32 ⟨48, 0, 0, 1, 1, 0⟩ ⟨49, 0, 0, 1, 1, 0⟩,
    .shl 32 ⟨51, 0, 0, 1, 1, 0⟩ ⟨48, 0, 0, 1, 1, 0⟩ 2,
    .add 32 ⟨52, 0, 0, 1, 1, 0⟩ ⟨51, 0, 0, 1, 1, 0⟩ ⟨50, 0, 0, 0, 1, 0⟩ ]

/-- The memory half: load through `V0053`, add one, store, return. -/
def realAddOneTail : List RInstr :=
  [ .load 32 54 .d32 53,
    .addImm 32 ⟨55, 0, 0, 1, 1, 0⟩ ⟨54, 0, 0, 1, 1, 0⟩ 1 .w16,
    .store 32 53 .d32 55,
    .ret 1 ]

def realAddOneInstrs : List RInstr := realAddOnePreamble ++ realAddOneTail

/-- The decoder's output is exactly the instruction list above. -/
theorem realAddOne_decoded_eq :
    decodeRealProgram realAddOne = some realAddOneInstrs := by
  unfold decodeRealProgram decodeRealStmts realAddOne realAddOneInstrs
    realAddOnePreamble realAddOneTail
  decide

def Grf.simple (g : Grf) : Bool := g.width == 1 && g.hstride == 0

def Grf.dstSimple (g : Grf) : Bool :=
  g.row == 0 && g.col == 0 && g.simple

def RInstr.regionsSimple : RInstr → Bool
  | .prologue => true
  | .mul _ d a b => d.dstSimple && a.simple && b.simple
  | .mov _ d s => d.dstSimple && s.simple
  | .movMasked _ d s => d.dstSimple && s.simple
  | .add3 _ d a b c => d.dstSimple && a.simple && b.simple && c.simple
  | .shl _ d s _ => d.dstSimple && s.simple
  | .add _ d a b => d.dstSimple && a.simple && b.simple
  | .addImm _ d s _ _ => d.dstSimple && s.simple
  | .load _ _ _ _ => true
  | .store _ _ _ _ => true
  | .ret _ => true
  | .label _ => true
  | .movImm _ d _ _ => d.dstSimple
  | .or _ d a b => d.dstSimple && a.simple && b.simple
  | .cmpLt _ _ _ _ _ => true
  | .cmpLtReg _ _ _ _ => true
  | .cmpEqReg _ _ _ _ => true
  | .predAnd _ _ _ _ => true
  | .predOr _ _ _ _ => true
  | .goto _ _ => true
  | .gotoIf _ _ _ _ => true
  | .loadScaled _ _ _ _ _ => true
  | .storeScaled _ _ _ _ _ => true
  | .sel _ _ d a b => d.dstSimple && a.simple && b.simple

/-- The region interpretation used by `stepReal` is exactly what this kernel
prints: dense destinations at `(0,0)`, width 1, horizontal stride 0. -/
theorem realAddOne_regions_simple :
    realAddOneInstrs.all RInstr.regionsSimple = true := by
  unfold realAddOneInstrs realAddOnePreamble realAddOneTail
  decide

/-- The launch facts the kernel relies on: the base pointer, the enqueued
local size, `r0[1]`, the per-lane local id, and the global offset. -/
structure LaunchPre (s : RealState) (base : Addr) (localSize r0 : Word)
    (localId : Nat → BitVec 16) (globalOffset : Word) : Prop where
  baseReg : s.regs 34 0 = base
  localSizeReg : s.regs 38 0 = zext localSize
  r0Reg : s.regs 36 1 = zext r0
  localIdReg : ∀ l, s.regs 39 l = (localId l).zeroExtend 64
  offsetReg : s.regs 37 0 = zext globalOffset

/-- The linear id computed by the preamble, matching `%8` in the source IR. -/
def threadId (localSize r0 : Word) (localId : Nat → BitVec 16)
    (globalOffset : Word) (l : Nat) : Word :=
  localSize * r0 + (localId l).zeroExtend 32 + globalOffset

/-- The byte address, matching `%12 = (%9 << 2) + %10`. -/
def realAddress (base : Addr) (id : Word) : Addr :=
  (zext id) <<< 2 + base

theorem realAddress_aligned (base : Addr) (id : Word) (h : base.toNat % 4 = 0) :
    (realAddress base id).toNat % 4 = 0 := by
  unfold realAddress
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft]
  omega

/-- The word at a lane's address in the initial memory. -/
def laneWord (s : RealState) (base : Addr) (id : Word) : Word :=
  s.mem ((realAddress base id).toNat / 4)


/-- Declared element counts, from the dump's `.decl` lines. -/
def regElems : Nat → Nat
  | 34 => 1
  | 36 => 8
  | 37 => 3
  | 38 => 3
  | 39 => 32
  | 44 => 1
  | 45 => 32
  | 46 => 32
  | 47 => 32
  | 48 => 32
  | 49 => 32
  | 50 => 1
  | 51 => 32
  | 52 => 32
  | 53 => 32
  | 54 => 32
  | 55 => 32
  | _ => 0

/-- Every destination register holds exactly as many elements as the
instruction's execution size writes. -/
def RInstr.dstCountOk : RInstr → Bool
  | .prologue => true
  | .mul n d _ _ => regElems d.num == n && (regType d.num).isSome
  | .mov n d _ => regElems d.num == n && (regType d.num).isSome
  | .movMasked n d _ => regElems d.num == n && (regType d.num).isSome
  | .add3 n d _ _ _ => regElems d.num == n && (regType d.num).isSome
  | .shl n d _ _ => regElems d.num == n && (regType d.num).isSome
  | .add n d _ _ => regElems d.num == n && (regType d.num).isSome
  | .addImm n d _ _ _ => regElems d.num == n && (regType d.num).isSome
  | .load n d _ _ => regElems d == n && (regType d).isSome
  | .store _ _ _ _ => true
  | .ret _ => true
  | .label _ => true
  | .movImm n d _ _ => regElems d.num == n && (regType d.num).isSome
  | .or n d _ _ => regElems d.num == n && (regType d.num).isSome
  | .cmpLt _ _ _ _ _ => true
  | .cmpLtReg _ _ _ _ => true
  | .cmpEqReg _ _ _ _ => true
  | .predAnd _ _ _ _ => true
  | .predOr _ _ _ _ => true
  | .goto _ _ => true
  | .gotoIf _ _ _ _ => true
  | .loadScaled n d _ _ _ => regElems d == n && (regType d).isSome
  | .storeScaled _ _ _ _ _ => true
  | .sel n _ d _ _ => regElems d.num == n && (regType d.num).isSome

/-- Every destination has a declared type and exactly as many elements as the
execution size writes, so writing the whole register is exact. -/
theorem realAddOne_dst_counts :
    realAddOneInstrs.all RInstr.dstCountOk = true := by
  unfold realAddOneInstrs realAddOnePreamble realAddOneTail
  decide

/-- `V0053`, the address register, holds the computed address at every lane.
`V0053` aliases `V0052`, so the state projection is at physical register 52. -/
theorem realAddOne_address_preamble (s : RealState) (base : Addr)
    (localSize r0 : Word) (localId : Nat → BitVec 16) (globalOffset : Word)
    (l : Nat) (h : LaunchPre s base localSize r0 localId globalOffset) :
    (runReal s realAddOnePreamble).regs 52 l =
      realAddress base (threadId localSize r0 localId globalOffset l) := by
  unfold realAddOnePreamble runReal threadId realAddress
  simp [runRealWith, stepWith, writeVecWith, setReg, readRegWith, readSrcWith,
    srcIndex, aliasBase, isWideOf, regType, RegType.is64, binOpWide, add3Wide,
    shlWide, h.baseReg, h.localSizeReg, h.r0Reg, h.localIdReg, h.offsetReg]

/-- The preamble only writes registers. -/
theorem realAddOne_preamble_mem (s : RealState) :
    (runReal s realAddOnePreamble).mem = s.mem := rfl

/-- The tail's memory after the load, add and store. -/
theorem realAddOne_tail_mem (s : RealState) (base : Addr) (localSize r0 : Word)
    (localId : Nat → BitVec 16) (globalOffset : Word)
    (haddr : ∀ l,
      s.regs 52 l = realAddress base (threadId localSize r0 localId globalOffset l)) :
    (runReal s realAddOneTail).mem =
      storeVec s.mem 32
        (fun l => realAddress base (threadId localSize r0 localId globalOffset l))
        (fun l =>
          laneWord s base (threadId localSize r0 localId globalOffset l) + 1) := by
  unfold realAddOneTail runReal
  simp [runRealWith, stepWith, writeVecWith, setReg, readRegWith, readSrcWith,
    srcIndex, aliasBase, isWideOf, regType, RegType.is64, addImmWide, load32,
    laneWord]
  have hfun : (fun l => s.regs 52 l) =
      (fun l => realAddress base (threadId localSize r0 localId globalOffset l)) :=
    funext haddr
  rw [hfun]
  congr 1
  funext l
  rw [haddr]

/-- Running the whole kernel leaves the store vector as the memory. -/
theorem realAddOne_mem (s : RealState) (base : Addr) (localSize r0 : Word)
    (localId : Nat → BitVec 16) (globalOffset : Word)
    (h : LaunchPre s base localSize r0 localId globalOffset) :
    (runReal s realAddOneInstrs).mem =
      storeVec s.mem 32
        (fun l => realAddress base (threadId localSize r0 localId globalOffset l))
        (fun l =>
          laneWord s base (threadId localSize r0 localId globalOffset l) + 1) := by
  unfold realAddOneInstrs
  rw [runReal_append]
  have haddr : ∀ l,
      (runReal s realAddOnePreamble).regs 52 l =
        realAddress base (threadId localSize r0 localId globalOffset l) :=
    fun l => realAddOne_address_preamble s base localSize r0 localId globalOffset l h
  rw [realAddOne_tail_mem (runReal s realAddOnePreamble) base localSize r0 localId
    globalOffset haddr]
  simp only [laneWord]
  rw [realAddOne_preamble_mem]

/-- The kernel halts: `ret` is the last instruction. -/
theorem realAddOne_halted (s : RealState) :
    (runReal s realAddOneInstrs).halted = true := by
  unfold realAddOneInstrs realAddOnePreamble realAddOneTail runReal
  simp [runRealWith, stepWith, writeVecWith]

/-- End to end for the real kernel: each of the 32 lanes computes an aligned
address, increments the word originally there, and no other word changes.
Distinct word addresses are the race-freedom hypothesis. -/
theorem realAddOne_effect (s : RealState) (base : Addr) (localSize r0 : Word)
    (localId : Nat → BitVec 16) (globalOffset : Word)
    (h : LaunchPre s base localSize r0 localId globalOffset)
    (halign : base.toNat % 4 = 0)
    (hdistinct : ∀ k l, k < 32 → l < 32 → k ≠ l →
      (realAddress base (threadId localSize r0 localId globalOffset k)).toNat / 4 ≠
        (realAddress base (threadId localSize r0 localId globalOffset l)).toNat / 4) :
    (runReal s realAddOneInstrs).halted = true ∧
    (∀ l, l < 32 →
      (realAddress base (threadId localSize r0 localId globalOffset l)).toNat % 4 = 0) ∧
    (∀ l, l < 32 →
      (runReal s realAddOneInstrs).mem
        ((realAddress base (threadId localSize r0 localId globalOffset l)).toNat / 4) =
      laneWord s base (threadId localSize r0 localId globalOffset l) + 1) ∧
    (∀ w, (∀ l, l < 32 →
        (realAddress base (threadId localSize r0 localId globalOffset l)).toNat / 4 ≠ w) →
      (runReal s realAddOneInstrs).mem w = s.mem w) := by
  refine ⟨realAddOne_halted s, ?_, ?_, ?_⟩
  · intro l _
    exact realAddress_aligned base _ halign
  · intro l hl
    rw [realAddOne_mem s base localSize r0 localId globalOffset h]
    exact storeVec_same s.mem 32 _ _ l hl
      (fun k hk hne => hdistinct k l hk hl hne)
  · intro w hw
    rw [realAddOne_mem s base localSize r0 localId globalOffset h]
    exact storeVec_frame s.mem 32 _ _ w hw

end

/-- `cmp.lt` writes the per-lane comparison on active lanes. -/
theorem cmpLt_lane (alias : Nat → Nat) (typeOf : Nat → Option RegType)
    (s : RealState) (e : Exec) (p imm : Nat) (src : Grf) (w : Width) (l : Nat)
    (hl : l < e.size) :
    (stepWith alias typeOf s (.cmpLt e p src imm w)).preds p l =
      decide (low32 (readSrcWith alias s src l) < BitVec.ofNat 32 imm) := by
  simp [stepWith, hl]

/-- A different predicate is untouched. -/
theorem cmpLt_other (alias : Nat → Nat) (typeOf : Nat → Option RegType)
    (s : RealState) (e : Exec) (p imm : Nat) (src : Grf) (w : Width) (p' l : Nat)
    (hp : p' ≠ p) :
    (stepWith alias typeOf s (.cmpLt e p src imm w)).preds p' l = s.preds p' l := by
  simp [stepWith, hp]

/-- A lane outside the execution size is untouched. -/
theorem cmpLt_inactive (alias : Nat → Nat) (typeOf : Nat → Option RegType)
    (s : RealState) (e : Exec) (p imm : Nat) (src : Grf) (w : Width) (l : Nat)
    (hl : ¬ l < e.size) :
    (stepWith alias typeOf s (.cmpLt e p src imm w)).preds p l = s.preds p l := by
  simp [stepWith, hl]

/-- Predicate `and` combines the two source predicates on active lanes. -/
theorem predAnd_lane (alias : Nat → Nat) (typeOf : Nat → Option RegType)
    (s : RealState) (e : Exec) (p a b : Nat) (l : Nat) (hl : l < e.size) :
    (stepWith alias typeOf s (.predAnd e p a b)).preds p l =
      (s.preds a l && s.preds b l) := by
  simp [stepWith, hl]

/-- A different predicate is untouched by `and`. -/
theorem predAnd_other (alias : Nat → Nat) (typeOf : Nat → Option RegType)
    (s : RealState) (e : Exec) (p a b : Nat) (p' l : Nat) (hp : p' ≠ p) :
    (stepWith alias typeOf s (.predAnd e p a b)).preds p' l = s.preds p' l := by
  simp [stepWith, hp]

/-- A lane outside the execution size is untouched by `and`. -/
theorem predAnd_inactive (alias : Nat → Nat) (typeOf : Nat → Option RegType)
    (s : RealState) (e : Exec) (p a b : Nat) (l : Nat) (hl : ¬ l < e.size) :
    (stepWith alias typeOf s (.predAnd e p a b)).preds p l = s.preds p l := by
  simp [stepWith, hl]

/-- Predicate `or` combines the two source predicates on active lanes. -/
theorem predOr_lane (alias : Nat → Nat) (typeOf : Nat → Option RegType)
    (s : RealState) (e : Exec) (p a b : Nat) (l : Nat) (hl : l < e.size) :
    (stepWith alias typeOf s (.predOr e p a b)).preds p l =
      (s.preds a l || s.preds b l) := by
  simp [stepWith, hl]

/-- A different predicate is untouched by `or`. -/
theorem predOr_other (alias : Nat → Nat) (typeOf : Nat → Option RegType)
    (s : RealState) (e : Exec) (p a b : Nat) (p' l : Nat) (hp : p' ≠ p) :
    (stepWith alias typeOf s (.predOr e p a b)).preds p' l = s.preds p' l := by
  simp [stepWith, hp]

/-- A lane outside the execution size is untouched by `or`. -/
theorem predOr_inactive (alias : Nat → Nat) (typeOf : Nat → Option RegType)
    (s : RealState) (e : Exec) (p a b : Nat) (l : Nat) (hl : ¬ l < e.size) :
    (stepWith alias typeOf s (.predOr e p a b)).preds p l = s.preds p l := by
  simp [stepWith, hl]

/-- Register-register `cmp.lt` compares the low 32 bits on active lanes. -/
theorem cmpLtReg_lane (alias : Nat → Nat) (typeOf : Nat → Option RegType)
    (s : RealState) (e : Exec) (p : Nat) (a b : Grf) (l : Nat) (hl : l < e.size) :
    (stepWith alias typeOf s (.cmpLtReg e p a b)).preds p l =
      decide (low32 (readSrcWith alias s a l) < low32 (readSrcWith alias s b l)) := by
  simp [stepWith, hl]

/-- A different predicate is untouched by register `cmp.lt`. -/
theorem cmpLtReg_other (alias : Nat → Nat) (typeOf : Nat → Option RegType)
    (s : RealState) (e : Exec) (p : Nat) (a b : Grf) (p' l : Nat) (hp : p' ≠ p) :
    (stepWith alias typeOf s (.cmpLtReg e p a b)).preds p' l = s.preds p' l := by
  simp [stepWith, hp]

/-- An inactive lane is untouched by register `cmp.lt`. -/
theorem cmpLtReg_inactive (alias : Nat → Nat) (typeOf : Nat → Option RegType)
    (s : RealState) (e : Exec) (p : Nat) (a b : Grf) (l : Nat) (hl : ¬ l < e.size) :
    (stepWith alias typeOf s (.cmpLtReg e p a b)).preds p l = s.preds p l := by
  simp [stepWith, hl]

/-- Register-register `cmp.eq` compares the low 32 bits on active lanes. -/
theorem cmpEqReg_lane (alias : Nat → Nat) (typeOf : Nat → Option RegType)
    (s : RealState) (e : Exec) (p : Nat) (a b : Grf) (l : Nat) (hl : l < e.size) :
    (stepWith alias typeOf s (.cmpEqReg e p a b)).preds p l =
      decide (low32 (readSrcWith alias s a l) = low32 (readSrcWith alias s b l)) := by
  simp [stepWith, hl]

/-- A different predicate is untouched by register `cmp.eq`. -/
theorem cmpEqReg_other (alias : Nat → Nat) (typeOf : Nat → Option RegType)
    (s : RealState) (e : Exec) (p : Nat) (a b : Grf) (p' l : Nat) (hp : p' ≠ p) :
    (stepWith alias typeOf s (.cmpEqReg e p a b)).preds p' l = s.preds p' l := by
  simp [stepWith, hp]

/-- An inactive lane is untouched by register `cmp.eq`. -/
theorem cmpEqReg_inactive (alias : Nat → Nat) (typeOf : Nat → Option RegType)
    (s : RealState) (e : Exec) (p : Nat) (a b : Grf) (l : Nat) (hl : ¬ l < e.size) :
    (stepWith alias typeOf s (.cmpEqReg e p a b)).preds p l = s.preds p l := by
  simp [stepWith, hl]

/-- A predicated select reads `a` on true lanes and `b` on false lanes. -/
theorem sel_lane (alias : Nat → Nat) (typeOf : Nat → Option RegType)
    (s : RealState) (e : Exec) (p : Nat) (dst a b : Grf) (l : Nat) :
    (stepWith alias typeOf s (.sel e p dst a b)).regs (alias dst.num) l =
      if s.preds p l then readSrcWith alias s a l else readSrcWith alias s b l := by
  simp [stepWith, writeVecWith, setReg]

/-- A masked move with a unit-stride destination writes each active lane's
source element at the corresponding destination-region element. -/
theorem maskedMov_unit_lane (alias : Nat → Nat) (typeOf : Nat → Option RegType)
    (s : RealState) (e : Exec) (dst src : Grf) (l : Nat)
    (hnm : e.noMask = false) (hdst : dst.hstride = 1)
    (hactive : e.laneActive l = true) :
    (stepWith alias typeOf s (.movMasked e dst src)).regs (alias dst.num)
        (dst.dstIndex (e.laneIndex l)) =
      readSrcIndexed alias s src (e.laneIndex l) := by
  have hle : e.offset ≤ l := by
    have h := hactive
    simp [Exec.laneActive, hnm] at h
    exact h.1
  simp [stepWith, writeMaskedWith, Grf.dstIndex, Exec.laneIndex, hnm, hdst,
    Nat.add_sub_of_le hle, hactive]

/-- A masked move with a stride-two destination writes each active lane's
source element at `base + 2 * (lane - maskOffset)`. -/
theorem maskedMov_stride2_lane (alias : Nat → Nat) (typeOf : Nat → Option RegType)
    (s : RealState) (e : Exec) (dst src : Grf) (l : Nat)
    (hnm : e.noMask = false) (hdst : dst.hstride = 2)
    (hactive : e.laneActive l = true) :
    (stepWith alias typeOf s (.movMasked e dst src)).regs (alias dst.num)
        (dst.dstIndex (e.laneIndex l)) =
      readSrcIndexed alias s src (e.laneIndex l) := by
  have hle : e.offset ≤ l := by
    have h := hactive
    simp [Exec.laneActive, hnm] at h
    exact h.1
  have hmod : (l - e.offset) * 2 % 2 = 0 := by
    rw [Nat.mul_comm]
    exact Nat.mul_mod_right 2 (l - e.offset)
  have hdiv : (l - e.offset) * 2 / 2 = l - e.offset := by
    rw [Nat.mul_comm]
    exact Nat.mul_div_right (l - e.offset) (by decide : 0 < 2)
  simp [stepWith, writeMaskedWith, Grf.dstIndex, Exec.laneIndex, hnm, hdst,
    Nat.add_sub_of_le hle, hactive, hmod, hdiv]

/-- A masked move writes only its destination register; predicates, memory and
the halt flag are untouched. -/
theorem maskedMov_frame (alias : Nat → Nat) (typeOf : Nat → Option RegType)
    (s : RealState) (e : Exec) (dst src : Grf) :
    (stepWith alias typeOf s (.movMasked e dst src)).preds = s.preds ∧
    (stepWith alias typeOf s (.movMasked e dst src)).mem = s.mem ∧
    (stepWith alias typeOf s (.movMasked e dst src)).halted = s.halted := by
  simp [stepWith, writeMaskedWith]

/-- A masked move leaves every other register's elements untouched. -/
theorem maskedMov_other_reg (alias : Nat → Nat) (typeOf : Nat → Option RegType)
    (s : RealState) (e : Exec) (dst src : Grf) (r j : Nat)
    (h : alias r ≠ alias dst.num) :
    (stepWith alias typeOf s (.movMasked e dst src)).regs (alias r) j =
      s.regs (alias r) j := by
  simp [stepWith, writeMaskedWith, h]

/-- The M5 channel offset is load-bearing: lane 0 is inactive, lane 16 is
active, and treating the instruction as M1 would disable lane 16. -/
theorem mask_offset_load_bearing :
    Exec.laneActive ⟨16, 16, false⟩ 0 = false ∧
    Exec.laneActive ⟨16, 16, false⟩ 16 = true ∧
    Exec.laneActive ⟨16, 0, false⟩ 16 = false := by
  decide

end IntelGpu
