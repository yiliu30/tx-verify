-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaAddr
public import Intel.TlaAluState

@[expose] public section

/-!
# Executing the SYCL-TLA block2d loads and stores

`Intel/TlaAddr.lean` parses the block2d address operands but does not give them
a value. This module turns a parsed operand into an effective address and gives
the 393 block2d instructions a load/store semantics over a tile-addressed
memory.

The memory model is deliberately coarse: a tile is identified by its effective
base address and carries one word per lane. Swizzles, row/column geometry and
partial tiles are refinements of `TlaMem`, not of the instruction semantics.

The effective address of
* `ss[aN.M][rB:S-off]` is `addr aN.M + regs B S - off`,
* `bti[N][rB:S+off]` is `bti N + regs B S + off`,
* `[rB:S]` is `regs B S`.

`tlaBlock2dLoad?` writes the tile into the destination region through
`writeTlaMasked`; `tlaBlock2dStore?` writes the active destination elements back
into the tile. The main theorems are that loads leave memory unchanged, stores
leave the register state unchanged, an active store followed by a load returns
the stored register value, and a load followed by a store is a memory no-op.
-/

namespace IntelGpu

/-- The three address forms of the dump. -/
inductive TlaSpace where
  | ss
  | bti
  | flat
  deriving Repr, DecidableEq

/-- Classify the textual address space. -/
def TlaAddr.kind (a : TlaAddr) : TlaSpace :=
  if a.space = "ss" then .ss else if a.space = "bti" then .bti else .flat

/-- The signed immediate offset of a parsed operand. -/
def TlaAddr.offsetWord (a : TlaAddr) : Word :=
  if a.neg then -BitVec.ofNat 32 a.offset else BitVec.ofNat 32 a.offset

/-- Effective address of a parsed block2d operand. -/
def TlaAddr.effAddr (st : TlaState) (bti : Nat → Word) (a : TlaAddr) : Word :=
  let base := st.regs a.base a.baseSub + a.offsetWord
  match a.kind with
  | .ss => st.addr a.reg a.sub + base
  | .bti => bti a.reg + base
  | .flat => base

theorem kind_ss :
    (⟨"ss", 0, 2, 2, 1, 0xE2C0, true⟩ : TlaAddr).kind = .ss := by decide

theorem kind_bti :
    (⟨"bti", 255, 0, 127, 1, 0, false⟩ : TlaAddr).kind = .bti := by decide

theorem kind_flat :
    (⟨"flat", 0, 0, 4, 1, 0, false⟩ : TlaAddr).kind = .flat := by decide

/-- The shared-memory form: address register plus base register minus offset. -/
theorem effAddr_ss (st : TlaState) (bti : Nat → Word) :
    (⟨"ss", 0, 2, 2, 1, 0xE2C0, true⟩ : TlaAddr).effAddr st bti =
      st.addr 0 2 + (st.regs 2 1 + (-(0xE2C0 : Word))) := by
  simp [TlaAddr.effAddr, TlaAddr.offsetWord, TlaAddr.kind]

/-- The binding-table form: table entry plus base register plus offset. -/
theorem effAddr_bti_pos (st : TlaState) (bti : Nat → Word) :
    (⟨"bti", 255, 0, 127, 1, 0x100, false⟩ : TlaAddr).effAddr st bti =
      bti 255 + (st.regs 127 1 + 0x100) := by
  simp [TlaAddr.effAddr, TlaAddr.offsetWord, TlaAddr.kind]

/-- The flat form: just the base register. -/
theorem effAddr_flat (st : TlaState) (bti : Nat → Word) :
    (⟨"flat", 0, 0, 4, 1, 0, false⟩ : TlaAddr).effAddr st bti = st.regs 4 1 := by
  simp [TlaAddr.effAddr, TlaAddr.offsetWord, TlaAddr.kind]

/-- A tile-addressed memory: the first index is a tile base address, the
second a lane. -/
structure TlaMem where
  cells : Nat → Nat → Word

namespace TlaMem

def loadTile (m : TlaMem) (ea : Word) (lane : Nat) : Word :=
  m.cells ea.toNat lane

def storeTile (m : TlaMem) (ea : Word) (f : Nat → Word) : TlaMem :=
  { cells := fun b lane => if b = ea.toNat then f lane else m.cells b lane }

theorem loadTile_storeTile_same (m : TlaMem) (ea : Word) (f : Nat → Word)
    (lane : Nat) : (m.storeTile ea f).loadTile ea lane = f lane := by
  simp [loadTile, storeTile]

theorem loadTile_storeTile_other (m : TlaMem) (ea ea' : Word) (f : Nat → Word)
    (lane : Nat) (h : ea' ≠ ea) :
    (m.storeTile ea f).loadTile ea' lane = m.loadTile ea' lane := by
  have h' : ea'.toNat ≠ ea.toNat := fun hc => h (BitVec.toNat_inj.mp hc)
  simp [loadTile, storeTile, h']

theorem storeTile_same (m : TlaMem) (ea : Word) :
    m.storeTile ea (fun lane => m.loadTile ea lane) = m := by
  cases m with
  | mk cells =>
      simp only [storeTile, loadTile]
      congr 1
      funext b lane
      by_cases h : b = ea.toNat
      · subst h
        simp
      · simp [h]

end TlaMem

/-- The machine state: scalar banks, tile memory and binding table. -/
structure TlaMachine where
  state : TlaState
  mem : TlaMem
  bti : Nat → Word

/-- The element index the execution mask applies to. -/
def Exec.laneForElement (e : Exec) (i : Nat) : Nat :=
  if e.noMask then i else e.offset + i

/-- Whether region element `i` is written by the execution mask. -/
def Exec.elementActive (e : Exec) (i : Nat) : Bool :=
  e.laneActive (e.laneForElement i)

/-- Effective address of a decoded block2d instruction, if its operand
parses. -/
def TlaBlock2d.effAddr? (st : TlaState) (bti : Nat → Word) (b : TlaBlock2d) :
    Option Word :=
  (parseTlaAddr b.addr).map (fun a => a.effAddr st bti)

/-- An active unit-stride destination element receives the tile value. -/
theorem writeTlaMasked_element (rf : RegFile) (g : Grf) (e : Exec) (f : Nat → Word)
    (i : Nat) (hd : g.hstride = 1) (ha : e.elementActive i = true) :
    writeTlaMasked rf g e f g.num (g.dstIndex i) = f i := by
  have hb : g.row * 8 + g.col ≤ g.dstIndex i := by
    simp [Grf.dstIndex, hd]
  have hk : g.dstIndex i - (g.row * 8 + g.col) = i := by
    simp [Grf.dstIndex, hd]
  have ha' : e.laneActive (if e.noMask then i else e.offset + i) = true := by
    simpa [Exec.elementActive, Exec.laneForElement] using ha
  simp [writeTlaMasked, hd, hb, hk, ha']

/-- A load writes the memory tile into the destination region and leaves the
memory unchanged. -/
def tlaBlock2dLoad? (st : TlaState) (m : TlaMem) (bti : Nat → Word)
    (g : Grf) (b : TlaBlock2d) : Option (TlaState × TlaMem) := do
  let a ← parseTlaAddr b.addr
  let ea := a.effAddr st bti
  return ({ st with regs := writeTlaMasked st.regs g b.exec (fun l => m.loadTile ea l) }, m)

/-- A store writes the active destination elements into the memory tile and
leaves the register state unchanged. -/
def tlaBlock2dStore? (st : TlaState) (m : TlaMem) (bti : Nat → Word)
    (g : Grf) (b : TlaBlock2d) : Option (TlaState × TlaMem) := do
  let a ← parseTlaAddr b.addr
  let ea := a.effAddr st bti
  return (st, m.storeTile ea (fun l =>
    if b.exec.elementActive l then st.regs g.num (g.dstIndex l) else m.loadTile ea l))

theorem tlaBlock2dLoad?_mem (st : TlaState) (m : TlaMem) (bti : Nat → Word)
    (g : Grf) (b : TlaBlock2d) (p : TlaState × TlaMem)
    (h : tlaBlock2dLoad? st m bti g b = some p) : p.2 = m := by
  cases hp : parseTlaAddr b.addr with
  | none => simp [tlaBlock2dLoad?, hp] at h
  | some a =>
      simp [tlaBlock2dLoad?, hp] at h
      cases h
      rfl

theorem tlaBlock2dLoad?_frame (st : TlaState) (m : TlaMem) (bti : Nat → Word)
    (g : Grf) (b : TlaBlock2d) (p : TlaState × TlaMem)
    (h : tlaBlock2dLoad? st m bti g b = some p) (r j : Nat) (hr : r ≠ g.num) :
    p.1.regs r j = st.regs r j := by
  cases hp : parseTlaAddr b.addr with
  | none => simp [tlaBlock2dLoad?, hp] at h
  | some a =>
      simp [tlaBlock2dLoad?, hp] at h
      cases h
      simp [writeTlaMasked, hr]

theorem tlaBlock2dLoad?_active (st : TlaState) (m : TlaMem) (bti : Nat → Word)
    (g : Grf) (b : TlaBlock2d) (p : TlaState × TlaMem)
    (h : tlaBlock2dLoad? st m bti g b = some p) (a : TlaAddr)
    (hp : parseTlaAddr b.addr = some a) (i : Nat) (hd : g.hstride = 1)
    (ha : b.exec.elementActive i = true) :
    p.1.regs g.num (g.dstIndex i) = m.loadTile (a.effAddr st bti) i := by
  let f : Nat → Word := fun l => m.loadTile (a.effAddr st bti) l
  have hstep : tlaBlock2dLoad? st m bti g b =
      some ({ st with regs := writeTlaMasked st.regs g b.exec f }, m) := by
    simp [tlaBlock2dLoad?, hp, f]
  rw [hstep] at h
  cases h
  exact writeTlaMasked_element st.regs g b.exec f i hd ha

theorem tlaBlock2dStore?_regs (st : TlaState) (m : TlaMem) (bti : Nat → Word)
    (g : Grf) (b : TlaBlock2d) (p : TlaState × TlaMem)
    (h : tlaBlock2dStore? st m bti g b = some p) : p.1 = st := by
  cases hp : parseTlaAddr b.addr with
  | none => simp [tlaBlock2dStore?, hp] at h
  | some a =>
      simp [tlaBlock2dStore?, hp] at h
      cases h
      rfl

theorem tlaBlock2dStore?_lane (st : TlaState) (m : TlaMem) (bti : Nat → Word)
    (g : Grf) (b : TlaBlock2d) (p : TlaState × TlaMem)
    (h : tlaBlock2dStore? st m bti g b = some p) (a : TlaAddr)
    (hp : parseTlaAddr b.addr = some a) (lane : Nat) :
    p.2.loadTile (a.effAddr st bti) lane =
      if b.exec.elementActive lane then st.regs g.num (g.dstIndex lane)
      else m.loadTile (a.effAddr st bti) lane := by
  let f : Nat → Word := fun l =>
    if b.exec.elementActive l then st.regs g.num (g.dstIndex l)
    else m.loadTile (a.effAddr st bti) l
  have hstep : tlaBlock2dStore? st m bti g b =
      some (st, m.storeTile (a.effAddr st bti) f) := by
    simp [tlaBlock2dStore?, hp, f]
  rw [hstep] at h
  cases h
  exact TlaMem.loadTile_storeTile_same m (a.effAddr st bti) f lane

theorem tlaBlock2dStore?_frame (st : TlaState) (m : TlaMem) (bti : Nat → Word)
    (g : Grf) (b : TlaBlock2d) (p : TlaState × TlaMem)
    (h : tlaBlock2dStore? st m bti g b = some p) (a : TlaAddr)
    (hp : parseTlaAddr b.addr = some a) (ea' : Word)
    (hne : ea' ≠ a.effAddr st bti) (lane : Nat) :
    p.2.loadTile ea' lane = m.loadTile ea' lane := by
  let f : Nat → Word := fun l =>
    if b.exec.elementActive l then st.regs g.num (g.dstIndex l)
    else m.loadTile (a.effAddr st bti) l
  have hstep : tlaBlock2dStore? st m bti g b =
      some (st, m.storeTile (a.effAddr st bti) f) := by
    simp [tlaBlock2dStore?, hp, f]
  rw [hstep] at h
  cases h
  exact TlaMem.loadTile_storeTile_other m _ ea' f lane hne

/-- A load whose destination region does not contain the address base
register keeps the effective address fixed. -/
theorem TlaAddr.effAddr_writeTlaMasked (st : TlaState) (g : Grf) (e : Exec)
    (f : Nat → Word) (bti : Nat → Word) (a : TlaAddr) (h : a.base ≠ g.num) :
    a.effAddr { st with regs := writeTlaMasked st.regs g e f } bti =
      a.effAddr st bti := by
  simp [TlaAddr.effAddr, writeTlaMasked, h]

/-- Storing an active destination element and loading it back returns the
stored register value. -/
theorem tlaBlock2d_store_load_regs (st : TlaState) (m : TlaMem) (bti : Nat → Word)
    (g : Grf) (b : TlaBlock2d) (a : TlaAddr)
    (hp : parseTlaAddr b.addr = some a) (i : Nat) (hd : g.hstride = 1)
    (ha : b.exec.elementActive i = true) :
    ∃ m' st', tlaBlock2dStore? st m bti g b = some (st, m') ∧
      tlaBlock2dLoad? st m' bti g b = some (st', m') ∧
      st'.regs g.num (g.dstIndex i) = st.regs g.num (g.dstIndex i) := by
  let m' := m.storeTile (a.effAddr st bti) (fun l =>
    if b.exec.elementActive l then st.regs g.num (g.dstIndex l)
    else m.loadTile (a.effAddr st bti) l)
  let f : Nat → Word := fun l => m'.loadTile (a.effAddr st bti) l
  let st' : TlaState := { st with regs := writeTlaMasked st.regs g b.exec f }
  have hstore : tlaBlock2dStore? st m bti g b = some (st, m') := by
    simp [tlaBlock2dStore?, hp, m']
  have hload : tlaBlock2dLoad? st m' bti g b = some (st', m') := by
    simp [tlaBlock2dLoad?, hp, st', f]
  refine ⟨m', st', hstore, hload, ?_⟩
  simp [st', f, m', TlaMem.loadTile, TlaMem.storeTile, writeTlaMasked_element, hd, ha]

/-- Loading a tile and storing the very same destination region back is a
memory no-op, provided the destination region does not contain the address
base register. -/
theorem tlaBlock2d_load_store_mem (st : TlaState) (m : TlaMem) (bti : Nat → Word)
    (g : Grf) (b : TlaBlock2d) (a : TlaAddr)
    (hp : parseTlaAddr b.addr = some a) (hd : g.hstride = 1)
    (hbase : a.base ≠ g.num) :
    ∃ st', tlaBlock2dLoad? st m bti g b = some (st', m) ∧
      tlaBlock2dStore? st' m bti g b = some (st', m) := by
  let f : Nat → Word := fun l => m.loadTile (a.effAddr st bti) l
  let st' : TlaState := { st with regs := writeTlaMasked st.regs g b.exec f }
  have hload : tlaBlock2dLoad? st m bti g b = some (st', m) := by
    simp [tlaBlock2dLoad?, hp, st', f]
  have hfun : (fun l => if b.exec.elementActive l then
        st'.regs g.num (g.dstIndex l) else m.loadTile (a.effAddr st bti) l)
      = fun l => m.loadTile (a.effAddr st bti) l := by
    funext l
    by_cases hl : b.exec.elementActive l = true
    · rw [ite_eq_left hl]
      exact writeTlaMasked_element st.regs g b.exec _ l hd hl
    · rw [ite_eq_right hl]
  have heff : a.effAddr st' bti = a.effAddr st bti := by
    simp [st', TlaAddr.effAddr_writeTlaMasked, hbase]
  have hstore : tlaBlock2dStore? st' m bti g b = some (st', m) := by
    simp [tlaBlock2dStore?, hp, hfun, heff, TlaMem.storeTile_same]
  exact ⟨st', hload, hstore⟩

/-- The address space of a decoded block2d instruction. -/
def TlaBlock2d.spaceKind (b : TlaBlock2d) : Option TlaSpace :=
  (parseTlaAddr b.addr).map TlaAddr.kind

set_option maxRecDepth 100000 in
/-- 384 block2d operands use the shared-memory form. -/
theorem realTlaGemmBlock2d_ss_count :
    (realTlaGemmBlock2d.filter (fun b => b.spaceKind = some .ss)).length = 384 := by
  decide

set_option maxRecDepth 100000 in
/-- 4 block2d operands use the binding-table form. -/
theorem realTlaGemmBlock2d_bti_count :
    (realTlaGemmBlock2d.filter (fun b => b.spaceKind = some .bti)).length = 4 := by
  decide

set_option maxRecDepth 100000 in
/-- 5 block2d operands use the flat form. -/
theorem realTlaGemmBlock2d_flat_count :
    (realTlaGemmBlock2d.filter (fun b => b.spaceKind = some .flat)).length = 5 := by
  decide

/-- A parsed operand always yields an effective address. -/
theorem TlaBlock2d.effAddr?_isSome (st : TlaState) (bti : Nat → Word)
    (b : TlaBlock2d) (h : (parseTlaAddr b.addr).isSome = true) :
    (b.effAddr? st bti).isSome = true := by
  unfold TlaBlock2d.effAddr?
  cases hp : parseTlaAddr b.addr <;> simp [hp] at h ⊢

/-- Every block2d instruction computes an effective address. -/
theorem realTlaGemmBlock2d_effAddr (st : TlaState) (bti : Nat → Word) :
    realTlaGemmBlock2d.all (fun b => (b.effAddr? st bti).isSome) = true := by
  have h := realTlaGemmBlock2d_addr_parse
  rw [List.all_eq_true] at h
  rw [List.all_eq_true]
  intro b hb
  exact TlaBlock2d.effAddr?_isSome st bti b (of_decide_eq_true (h b hb))

end IntelGpu
