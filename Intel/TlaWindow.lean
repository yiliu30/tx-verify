-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaBlock2dExec
public import Intel.TlaBlockCensus

@[expose] public section

/-!
# Block2d register windows

The block2d data operand `rN:M` names `M` consecutive registers, each holding
eight dwords. This module parses that window, defines the lane mapping
`i ↦ (N + i/8, i%8)` and rewrites the block2d load/store steps over windows
instead of taking an arbitrary `Grf`.

All data operands except the six `null:0` loads have an `rN:M` window. The
two accumulator stores at PCs 1394 and 1395 use `r21:4` and `r25:4`, whose 64
lanes cover all 64 elements of the `r21..r28` C block.
-/

namespace IntelGpu

/-- A block of consecutive GRF registers. -/
structure TlaWindow where
  base : Nat
  count : Nat
  deriving Repr, DecidableEq

/-- Parse `rN:M`. -/
def parseTlaWindow (s : String) : Option TlaWindow :=
  match numRuns s with
  | [n, m] => some ⟨n, m⟩
  | _ => none

/-- The window of a decoded block2d instruction. -/
def TlaBlock2d.window? (b : TlaBlock2d) : Option TlaWindow :=
  parseTlaWindow b.reg

/-- The number of dword lanes in a window. -/
def TlaWindow.lanes (w : TlaWindow) : Nat := w.count * 8

/-- The register holding lane `i`. -/
def TlaWindow.laneReg (w : TlaWindow) (i : Nat) : Nat := w.base + i / 8

/-- The element holding lane `i`. -/
def TlaWindow.laneElem (_w : TlaWindow) (i : Nat) : Nat := i % 8

/-- The lane at register `r`, element `e`, if inside the window. -/
def TlaWindow.index (w : TlaWindow) (r e : Nat) : Option Nat :=
  if w.base ≤ r ∧ r < w.base + w.count ∧ e < 8 then
    some ((r - w.base) * 8 + e)
  else none

theorem TlaWindow.index_lane (w : TlaWindow) (i : Nat) (hi : i < w.lanes) :
    w.index (w.laneReg i) (w.laneElem i) = some i := by
  have h1 : w.base ≤ w.base + i / 8 := Nat.le_add_right _ _
  have h2 : w.base + i / 8 < w.base + w.count := by
    have hdiv : i / 8 < w.count := by
      have hi' : i < w.count * 8 := hi
      have h' : i < 8 * w.count := by rwa [Nat.mul_comm] at hi'
      exact Nat.div_lt_of_lt_mul h'
    omega
  have h3 : i % 8 < 8 := Nat.mod_lt _ (by decide)
  have h4 : w.base + i / 8 - w.base = i / 8 := by omega
  unfold TlaWindow.index TlaWindow.laneReg TlaWindow.laneElem
  rw [ite_eq_left ⟨h1, h2, h3⟩]
  congr 1
  rw [h4, Nat.mul_comm (i / 8) 8, Nat.div_add_mod]

theorem TlaWindow.index_none (w : TlaWindow) (r e : Nat)
    (h : ¬ (w.base ≤ r ∧ r < w.base + w.count ∧ e < 8)) :
    w.index r e = none := by
  simp [TlaWindow.index, h]

/-- Write the execution-masked source values into a window. -/
def writeWindow (rf : RegFile) (w : TlaWindow) (e : Exec) (f : Nat → Word) : RegFile :=
  fun r j => match w.index r j with
    | some i => if e.elementActive i then f i else rf r j
    | none => rf r j

theorem writeWindow_active (rf : RegFile) (w : TlaWindow) (e : Exec)
    (f : Nat → Word) (r j i : Nat) (hi : w.index r j = some i)
    (ha : e.elementActive i = true) :
    writeWindow rf w e f r j = f i := by
  simp [writeWindow, hi, ha]

theorem writeWindow_inactive (rf : RegFile) (w : TlaWindow) (e : Exec)
    (f : Nat → Word) (r j i : Nat) (hi : w.index r j = some i)
    (ha : e.elementActive i = false) :
    writeWindow rf w e f r j = rf r j := by
  simp [writeWindow, hi, ha]

theorem writeWindow_frame (rf : RegFile) (w : TlaWindow) (e : Exec)
    (f : Nat → Word) (r j : Nat) (h : w.index r j = none) :
    writeWindow rf w e f r j = rf r j := by
  simp [writeWindow, h]

/-- A block2d load into a register window. -/
def tlaBlock2dLoadW? (st : TlaState) (m : TlaMem) (bti : Nat → Word)
    (w : TlaWindow) (b : TlaBlock2d) : Option (TlaState × TlaMem) :=
  match parseTlaAddr b.addr with
  | none => none
  | some a =>
      let ea := a.effAddr st bti
      let rf := writeWindow st.regs w b.exec (fun l => m.loadTile ea l)
      some ({ st with regs := rf }, m)

/-- A block2d store from a register window. -/
def tlaBlock2dStoreW? (st : TlaState) (m : TlaMem) (bti : Nat → Word)
    (w : TlaWindow) (b : TlaBlock2d) : Option (TlaState × TlaMem) :=
  match parseTlaAddr b.addr with
  | none => none
  | some a =>
      let ea := a.effAddr st bti
      some (st, m.storeTile ea (fun l =>
        if b.exec.elementActive l then st.regs (w.laneReg l) (w.laneElem l)
        else m.loadTile ea l))

theorem tlaBlock2dLoadW?_mem (st : TlaState) (m : TlaMem) (bti : Nat → Word)
    (w : TlaWindow) (b : TlaBlock2d) (p : TlaState × TlaMem)
    (h : tlaBlock2dLoadW? st m bti w b = some p) : p.2 = m := by
  cases hp : parseTlaAddr b.addr with
  | none => simp [tlaBlock2dLoadW?, hp] at h
  | some a =>
      simp [tlaBlock2dLoadW?, hp] at h
      cases h
      rfl

theorem tlaBlock2dLoadW?_frame (st : TlaState) (m : TlaMem) (bti : Nat → Word)
    (w : TlaWindow) (b : TlaBlock2d) (p : TlaState × TlaMem)
    (h : tlaBlock2dLoadW? st m bti w b = some p) (r j : Nat)
    (hj : w.index r j = none) :
    p.1.regs r j = st.regs r j := by
  cases hp : parseTlaAddr b.addr with
  | none => simp [tlaBlock2dLoadW?, hp] at h
  | some a =>
      simp [tlaBlock2dLoadW?, hp] at h
      cases h
      exact writeWindow_frame st.regs w b.exec _ r j hj

theorem tlaBlock2dLoadW?_active (st : TlaState) (m : TlaMem) (bti : Nat → Word)
    (w : TlaWindow) (b : TlaBlock2d) (p : TlaState × TlaMem)
    (h : tlaBlock2dLoadW? st m bti w b = some p) (a : TlaAddr)
    (hp : parseTlaAddr b.addr = some a) (i : Nat) (hi : i < w.lanes)
    (ha : b.exec.elementActive i = true) :
    p.1.regs (w.laneReg i) (w.laneElem i) = m.loadTile (a.effAddr st bti) i := by
  let rf := writeWindow st.regs w b.exec (fun l => m.loadTile (a.effAddr st bti) l)
  have hstep : tlaBlock2dLoadW? st m bti w b = some ({ st with regs := rf }, m) := by
    simp [tlaBlock2dLoadW?, hp, rf]
  rw [hstep] at h
  cases h
  exact writeWindow_active st.regs w b.exec _ _ _ i (w.index_lane i hi) ha

theorem tlaBlock2dStoreW?_regs (st : TlaState) (m : TlaMem) (bti : Nat → Word)
    (w : TlaWindow) (b : TlaBlock2d) (p : TlaState × TlaMem)
    (h : tlaBlock2dStoreW? st m bti w b = some p) : p.1 = st := by
  cases hp : parseTlaAddr b.addr with
  | none => simp [tlaBlock2dStoreW?, hp] at h
  | some a =>
      simp [tlaBlock2dStoreW?, hp] at h
      cases h
      rfl

theorem tlaBlock2dStoreW?_lane (st : TlaState) (m : TlaMem) (bti : Nat → Word)
    (w : TlaWindow) (b : TlaBlock2d) (p : TlaState × TlaMem)
    (h : tlaBlock2dStoreW? st m bti w b = some p) (a : TlaAddr)
    (hp : parseTlaAddr b.addr = some a) (lane : Nat) :
    p.2.loadTile (a.effAddr st bti) lane =
      if b.exec.elementActive lane then st.regs (w.laneReg lane) (w.laneElem lane)
      else m.loadTile (a.effAddr st bti) lane := by
  have hstep : tlaBlock2dStoreW? st m bti w b =
      some (st, m.storeTile (a.effAddr st bti) (fun l =>
        if b.exec.elementActive l then st.regs (w.laneReg l) (w.laneElem l)
        else m.loadTile (a.effAddr st bti) l)) := by
    simp [tlaBlock2dStoreW?, hp]
  rw [hstep] at h
  cases h
  exact TlaMem.loadTile_storeTile_same m (a.effAddr st bti) _ lane

/-- A load into a window that misses the address base register keeps the
effective address fixed. -/
theorem TlaAddr.effAddr_writeWindow (st : TlaState) (w : TlaWindow) (e : Exec)
    (f : Nat → Word) (bti : Nat → Word) (a : TlaAddr)
    (h : w.index a.base a.baseSub = none) :
    a.effAddr { st with regs := writeWindow st.regs w e f } bti = a.effAddr st bti := by
  simp [TlaAddr.effAddr, writeWindow, h]

/-- Storing an active in-window lane and loading it back returns the stored
register value. -/
theorem tlaBlock2d_store_load_W_regs (st : TlaState) (m : TlaMem) (bti : Nat → Word)
    (w : TlaWindow) (b : TlaBlock2d) (a : TlaAddr)
    (hp : parseTlaAddr b.addr = some a) (i : Nat) (hi : i < w.lanes)
    (ha : b.exec.elementActive i = true) :
    ∃ m' st', tlaBlock2dStoreW? st m bti w b = some (st, m') ∧
      tlaBlock2dLoadW? st m' bti w b = some (st', m') ∧
      st'.regs (w.laneReg i) (w.laneElem i) = st.regs (w.laneReg i) (w.laneElem i) := by
  let m' := m.storeTile (a.effAddr st bti) (fun l =>
    if b.exec.elementActive l then st.regs (w.laneReg l) (w.laneElem l)
    else m.loadTile (a.effAddr st bti) l)
  let f : Nat → Word := fun l => m'.loadTile (a.effAddr st bti) l
  let st' : TlaState := { st with regs := writeWindow st.regs w b.exec f }
  have hstore : tlaBlock2dStoreW? st m bti w b = some (st, m') := by
    simp [tlaBlock2dStoreW?, hp, m']
  have hload : tlaBlock2dLoadW? st m' bti w b = some (st', m') := by
    simp [tlaBlock2dLoadW?, hp, st', f]
  refine ⟨m', st', hstore, hload, ?_⟩
  simp [st', f, m', TlaMem.loadTile, TlaMem.storeTile, writeWindow_active,
    w.index_lane i hi, ha]

/-- Loading a window and storing it back is a memory no-op when the window
misses the address base register. -/
theorem tlaBlock2d_load_store_W_mem (st : TlaState) (m : TlaMem) (bti : Nat → Word)
    (w : TlaWindow) (b : TlaBlock2d) (a : TlaAddr)
    (hp : parseTlaAddr b.addr = some a) (hbase : w.index a.base a.baseSub = none)
    (hact : ∀ l, b.exec.elementActive l = true → l < w.lanes) :
    ∃ st', tlaBlock2dLoadW? st m bti w b = some (st', m) ∧
      tlaBlock2dStoreW? st' m bti w b = some (st', m) := by
  let f : Nat → Word := fun l => m.loadTile (a.effAddr st bti) l
  let st' : TlaState := { st with regs := writeWindow st.regs w b.exec f }
  have hload : tlaBlock2dLoadW? st m bti w b = some (st', m) := by
    simp [tlaBlock2dLoadW?, hp, st', f]
  have hfun : (fun l => if b.exec.elementActive l then
        st'.regs (w.laneReg l) (w.laneElem l) else m.loadTile (a.effAddr st bti) l)
      = fun l => m.loadTile (a.effAddr st bti) l := by
    funext l
    by_cases hl : b.exec.elementActive l = true
    · rw [ite_eq_left hl]
      exact writeWindow_active st.regs w b.exec f _ _ l (w.index_lane l (hact l hl)) hl
    · rw [ite_eq_right hl]
  have heff : a.effAddr st' bti = a.effAddr st bti := by
    simp [st', TlaAddr.effAddr_writeWindow, hbase]
  have hstore : tlaBlock2dStoreW? st' m bti w b = some (st', m) := by
    simp [tlaBlock2dStoreW?, hp, hfun, heff, TlaMem.storeTile_same]
  exact ⟨st', hload, hstore⟩

set_option maxRecDepth 100000 in
/-- `r21:4` is the first accumulator window. -/
theorem parseTlaWindow_r21 : parseTlaWindow "r21:4" = some ⟨21, 4⟩ := by decide

set_option maxRecDepth 100000 in
/-- `r25:4` is the second accumulator window. -/
theorem parseTlaWindow_r25 : parseTlaWindow "r25:4" = some ⟨25, 4⟩ := by decide

set_option maxRecDepth 100000 in
/-- `r64:16` is the first B-operand window. -/
theorem parseTlaWindow_r64 : parseTlaWindow "r64:16" = some ⟨64, 16⟩ := by decide

set_option maxRecDepth 100000 in
/-- `null:0` has no window. -/
theorem parseTlaWindow_null : parseTlaWindow "null:0" = none := by decide

set_option maxRecDepth 100000 in
/-- PC 1385 loads the first accumulator window. -/
theorem blockAccLoad21 :
    (blockInstrs.find? (fun p => p.1 = 1385)).map (fun p => p.2) = some (.predicated "(W) load.ugm.d32x64t.a32"
      ["(1|M0)", "r21:4", "ss[a0.2][r2:1-0xF900]", "{$5}"]) := by decide

set_option maxRecDepth 100000 in
/-- PC 1387 loads the second accumulator window. -/
theorem blockAccLoad25 :
    (blockInstrs.find? (fun p => p.1 = 1387)).map (fun p => p.2) = some (.predicated "(W) load.ugm.d32x64t.a32"
      ["(1|M0)", "r25:4", "ss[a0.2][r2:1-0xF800]", "{$10}"]) := by decide

set_option maxRecDepth 100000 in
/-- PC 1394 stores the first accumulator window. -/
theorem blockAccStore21 :
    (blockInstrs.find? (fun p => p.1 = 1394)).map (fun p => p.2) = some (.predicated "(W) store.ugm.d32x64t.a32"
      ["(1|M0)", "ss[a0.2][r2:1-0xF900]", "r21:4", "{$11}"]) := by decide

set_option maxRecDepth 100000 in
/-- PC 1395 stores the second accumulator window. -/
theorem blockAccStore25 :
    (blockInstrs.find? (fun p => p.1 = 1395)).map (fun p => p.2) = some (.predicated "(W) store.ugm.d32x64t.a32"
      ["(1|M0)", "ss[a0.2][r2:1-0xF800]", "r25:4", "{$12}"]) := by decide

set_option maxRecDepth 100000 in
/-- PC 1394 decodes to the `r21:4` store. -/
theorem blockAccStore21_parsed :
    ((blockInstrs.find? (fun p => p.1 = 1394)).map (fun p => p.2)).bind parseTlaBlock2dInstr =
      some ⟨"(W) store.ugm.d32x64t.a32", ⟨1, 0, true⟩, "r21:4",
        "ss[a0.2][r2:1-0xF900]"⟩ := by decide

set_option maxRecDepth 100000 in
/-- PC 1395 decodes to the `r25:4` store. -/
theorem blockAccStore25_parsed :
    ((blockInstrs.find? (fun p => p.1 = 1395)).map (fun p => p.2)).bind parseTlaBlock2dInstr =
      some ⟨"(W) store.ugm.d32x64t.a32", ⟨1, 0, true⟩, "r25:4",
        "ss[a0.2][r2:1-0xF800]"⟩ := by decide

theorem window21_covers (m n : Nat) (hm : m < 4) (hn : n < 8) :
    (⟨21, 4⟩ : TlaWindow).index (21 + m) n = some (m * 8 + n) := by
  have hc : (⟨21, 4⟩ : TlaWindow).base ≤ 21 + m ∧
      21 + m < (⟨21, 4⟩ : TlaWindow).base + (⟨21, 4⟩ : TlaWindow).count ∧ n < 8 := by
    simp
    omega
  unfold TlaWindow.index
  rw [ite_eq_left hc]
  congr 1
  simp

theorem window25_covers (m n : Nat) (hm : 4 ≤ m) (hm' : m < 8) (hn : n < 8) :
    (⟨25, 4⟩ : TlaWindow).index (21 + m) n = some ((m - 4) * 8 + n) := by
  have hc : (⟨25, 4⟩ : TlaWindow).base ≤ 21 + m ∧
      21 + m < (⟨25, 4⟩ : TlaWindow).base + (⟨25, 4⟩ : TlaWindow).count ∧ n < 8 := by
    simp
    omega
  unfold TlaWindow.index
  rw [ite_eq_left hc]
  congr 1
  simp
  omega

end IntelGpu
