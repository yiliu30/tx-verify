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

`RealState.preds` is a uniform predicate file: `cmp.lt` writes lane 0's
comparison and `gotoIf` reads it. `runRealCF` interprets labels, `goto` and
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

def isWide (r : Nat) : Bool :=
  match regType r with
  | some t => t.is64
  | none => false

/-- A register file with 64-bit slots, word-addressed global memory and a halt
flag. -/
structure RealState where
  regs : Nat → Nat → Addr
  /-- Uniform predicate registers, one bit per predicate. `cmp.lt` is read at
  lane 0; the GEMM's control flow is uniform. -/
  preds : Nat → Bool
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

def readReg (s : RealState) (r e : Nat) : Addr := s.regs (aliasBase r) e

/-- Element index selected by a source region at lane `l`. All regions here
have width 1 and horizontal stride 0, so only the vertical stride decides
between a broadcast and a dense read. -/
def srcIndex (g : Grf) (l : Nat) : Nat :=
  g.row * 8 + g.col + if g.vstride = 0 then 0 else l

def readSrc (s : RealState) (g : Grf) (l : Nat) : Addr :=
  readReg s g.num (srcIndex g l)

def setReg (regs : Nat → Nat → Addr) (r : Nat) (g : Nat → Addr) : Nat → Nat → Addr :=
  fun r' e => if r' = r then g e else regs r' e

/-- Write all declared elements of a destination register. This is exact for
this kernel: every destination's `.decl` element count equals its execution
size, checked by `realAddOne_dst_counts`. -/
def writeVec (s : RealState) (r : Nat) (f : Nat → Addr) : RealState :=
  { s with regs := setReg s.regs (aliasBase r) f }

@[simp] theorem writeVec_same (s : RealState) (r : Nat) (f : Nat → Addr)
    (e : Nat) : (writeVec s r f).regs (aliasBase r) e = f e := by
  simp [writeVec, setReg]

@[simp] theorem writeVec_ne (s : RealState) (r : Nat) (f : Nat → Addr) (r' e : Nat)
    (h : aliasBase r' ≠ aliasBase r) :
    (writeVec s r f).regs (aliasBase r') e = s.regs (aliasBase r') e := by
  simp [writeVec, setReg, h]

abbrev low32 (a : Addr) : Word := a.truncate 32

abbrev zext (w : Word) : Addr := w.zeroExtend 64

@[simp] theorem low32_zext (w : Word) : low32 (zext w) = w := by
  bv_omega

@[simp] theorem low32_zext16 (w : BitVec 16) :
    low32 (w.zeroExtend 64) = w.zeroExtend 32 := by
  bv_omega

def binOp (dst : Nat) (f32 : Word → Word → Word) (f64 : Addr → Addr → Addr)
    (x y : Addr) : Addr :=
  if isWide dst then f64 x y else zext (f32 (low32 x) (low32 y))

def add3Op (dst : Nat) (x y z : Addr) : Addr :=
  if isWide dst then x + y + z else zext (low32 x + low32 y + low32 z)

def shlOp (dst : Nat) (x : Addr) (k : Nat) : Addr :=
  if isWide dst then x <<< k else zext (low32 x <<< k)

def addImmOp (dst : Nat) (x : Addr) (imm : Word) : Addr :=
  if isWide dst then x + zext imm else zext (low32 x + imm)

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

def stepReal : RealState → RInstr → RealState
  | s, .prologue => s
  | s, .mul _ dst a b =>
      writeVec s dst.num (fun l =>
        binOp dst.num (fun x y => x * y) (fun x y => x * y)
          (readSrc s a l) (readSrc s b l))
  | s, .mov _ dst src =>
      writeVec s dst.num (fun l => readSrc s src l)
  | s, .add3 _ dst a b c =>
      writeVec s dst.num (fun l =>
        add3Op dst.num (readSrc s a l) (readSrc s b l) (readSrc s c l))
  | s, .shl _ dst src k =>
      writeVec s dst.num (fun l => shlOp dst.num (readSrc s src l) k)
  | s, .add _ dst a b =>
      writeVec s dst.num (fun l =>
        binOp dst.num (fun x y => x + y) (fun x y => x + y)
          (readSrc s a l) (readSrc s b l))
  | s, .addImm _ dst src imm _ =>
      writeVec s dst.num (fun l =>
        addImmOp dst.num (readSrc s src l) (BitVec.ofNat 32 imm))
  | s, .load _ dst _ addrReg =>
      writeVec s dst (fun l => zext (load32 s.mem (readReg s addrReg l).toNat))
  | s, .store n addrReg _ src =>
      { s with
        mem := storeVec s.mem n (fun l => readReg s addrReg l)
          (fun l => low32 (readReg s src l)) }
  | s, .ret _ => { s with halted := true }
  | s, .label _ => s
  | s, .movImm _ dst imm _ =>
      writeVec s dst.num (fun _ => zext (BitVec.ofNat 32 imm))
  | s, .or _ dst a b =>
      writeVec s dst.num (fun l =>
        binOp dst.num (fun x y => x ||| y) (fun x y => x ||| y)
          (readSrc s a l) (readSrc s b l))
  | s, .cmpLt _ p src imm _ =>
      { s with
        preds := fun p' =>
          if p' = p then decide (low32 (readSrc s src 0) < BitVec.ofNat 32 imm)
          else s.preds p' }
  | s, .goto _ _ => s
  | s, .gotoIf _ _ _ _ => s

/-- The straight-line fold. It is the semantics used by the add-one proofs;
control flow is interpreted by `runRealCF`. -/
def runReal (s : RealState) (is : List RInstr) : RealState := is.foldl stepReal s

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
def runRealCF (code : List RInstr) (s : RealState) (pc fuel : Nat) : RealState :=
  match fuel with
  | 0 => s
  | fuel + 1 =>
      match code[pc]? with
      | none => s
      | some (.label _) => runRealCF code s (pc + 1) fuel
      | some (.goto _ l) =>
          match labelIndex code l with
          | some pc' => runRealCF code s pc' fuel
          | none => s
      | some (.gotoIf _ p negated l) =>
          let taken := if negated then !(s.preds p) else s.preds p
          if taken then
            match labelIndex code l with
            | some pc' => runRealCF code s pc' fuel
            | none => s
          else runRealCF code s (pc + 1) fuel
      | some i => runRealCF code (stepReal s i) (pc + 1) fuel

theorem runReal_append (s : RealState) (is js : List RInstr) :
    runReal s (is ++ js) = runReal (runReal s is) js := by
  simp [runReal, List.foldl_append]

/-- The address computation, as decoded: mul, two moves, add3, shift and add. -/
def realAddOnePreamble : List RInstr :=
  [ .prologue,
    .mul 1 ⟨44, 0, 0, 1, 1, 0⟩ ⟨38, 0, 0, 0, 1, 0⟩ ⟨36, 0, 1, 0, 1, 0⟩,
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
  | .goto _ _ => true
  | .gotoIf _ _ _ _ => true

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
  | .goto _ _ => true
  | .gotoIf _ _ _ _ => true

/-- Every destination has a declared type and exactly as many elements as the
execution size writes, so writing the whole register is exact. -/
theorem realAddOne_dst_counts :
    realAddOneInstrs.all RInstr.dstCountOk = true := by
  unfold realAddOneInstrs realAddOnePreamble realAddOneTail
  decide

/-- `V0053`, the address register, holds the computed address at every lane. -/
theorem realAddOne_address_preamble (s : RealState) (base : Addr)
    (localSize r0 : Word) (localId : Nat → BitVec 16) (globalOffset : Word)
    (l : Nat) (h : LaunchPre s base localSize r0 localId globalOffset) :
    readSrc (runReal s realAddOnePreamble) ⟨53, 0, 0, 1, 1, 0⟩ l =
      realAddress base (threadId localSize r0 localId globalOffset l) := by
  unfold realAddOnePreamble runReal threadId realAddress
  simp [stepReal, writeVec, setReg, readReg, readSrc, srcIndex, aliasBase,
    isWide, regType, RegType.is64, binOp, add3Op, shlOp, h.baseReg,
    h.localSizeReg, h.r0Reg, h.localIdReg, h.offsetReg]

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
  simp [stepReal, writeVec, setReg, readReg, readSrc, srcIndex, aliasBase, isWide,
    regType, RegType.is64, addImmOp, load32, laneWord]
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
        realAddress base (threadId localSize r0 localId globalOffset l) := by
    intro l
    simpa [readSrc, readReg, srcIndex, aliasBase] using
      realAddOne_address_preamble s base localSize r0 localId globalOffset l h
  rw [realAddOne_tail_mem (runReal s realAddOnePreamble) base localSize r0 localId
    globalOffset haddr]
  simp only [laneWord, realAddOne_preamble_mem]

/-- The kernel halts: `ret` is the last instruction. -/
theorem realAddOne_halted (s : RealState) :
    (runReal s realAddOneInstrs).halted = true := by
  unfold realAddOneInstrs realAddOnePreamble realAddOneTail runReal
  simp [stepReal, writeVec]

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

end IntelGpu