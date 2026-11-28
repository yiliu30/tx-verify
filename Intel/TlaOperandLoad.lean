-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaOperandWindow
public import Intel.TlaPlain

@[expose] public section

/-!
# The mainloop loads feed the DPAS operands

The five plain loads at PCs 979, 983, 986, 987 and 990 fill the B windows
`r64:16`, `r80:16`, `r96:16`, `r112:16` and the A window `r30:31`. This
module composes the window-load semantics with the operand-window bridge: the
DPAS read `readTileB (flat ·) base 0 k n` (resp. `readTileA · base m k`) after
the load is exactly the memory lane the load wrote.
-/

namespace IntelGpu

/-- A load into a 16-register window feeds the B tile read. -/
theorem loadWindow_feeds_readTileB (st : TlaState) (mem : TlaMem) (bti : Nat → Word)
    (b : TlaBlock2d) (base : Nat) (p : TlaState × TlaMem)
    (h : tlaBlock2dLoadW? st mem bti ⟨base, 16⟩ b = some p)
    (a : TlaAddr) (hp : parseTlaAddr b.addr = some a)
    (k n : Nat) (hk : k < 16) (hn : n < 8)
    (ha : b.exec.elementActive (bLane n k) = true) :
    readTileB (flat p.1.regs) base 0 k n =
      mem.loadTile (a.effAddr st bti) (bLane n k) := by
  let f : Nat → Word := fun l => mem.loadTile (a.effAddr st bti) l
  have hstep : tlaBlock2dLoadW? st mem bti ⟨base, 16⟩ b =
      some ({ st with regs := writeWindow st.regs ⟨base, 16⟩ b.exec f }, mem) := by
    simp [tlaBlock2dLoadW?, hp, f]
  rw [hstep] at h
  cases h
  exact readTileB_window st.regs b.exec f base k n hn hk ha

/-- A load into a 31-register window feeds the A tile read. -/
theorem loadWindow_feeds_readTileA (st : TlaState) (mem : TlaMem) (bti : Nat → Word)
    (b : TlaBlock2d) (base : Nat) (p : TlaState × TlaMem)
    (h : tlaBlock2dLoadW? st mem bti ⟨base, 31⟩ b = some p)
    (a : TlaAddr) (hp : parseTlaAddr b.addr = some a)
    (m k : Nat) (hm : m < 8) (hk : k < 16)
    (ha : b.exec.elementActive (aLane m k) = true) :
    readTileA p.1.regs base m k =
      mem.loadTile (a.effAddr st bti) (aLane m k) := by
  let f : Nat → Word := fun l => mem.loadTile (a.effAddr st bti) l
  have hstep : tlaBlock2dLoadW? st mem bti ⟨base, 31⟩ b =
      some ({ st with regs := writeWindow st.regs ⟨base, 31⟩ b.exec f }, mem) := by
    simp [tlaBlock2dLoadW?, hp, f]
  rw [hstep] at h
  cases h
  exact readTileA_window st.regs b.exec f base m k hm hk ha

/-- The first B-window load at PC 979. -/
def load979 : TlaBlock2d :=
  ⟨"load_block2d.ugm.d16v.a64", ⟨1, 0, true⟩, "r64:16", "[r7:1]"⟩

/-- The second B-window load at PC 983. -/
def load983 : TlaBlock2d :=
  ⟨"load_block2d.ugm.d16v.a64", ⟨1, 0, true⟩, "r80:16", "[r7:1]"⟩

/-- The A-window load at PC 986. -/
def load986 : TlaBlock2d :=
  ⟨"load_block2d.ugm.d16.a64", ⟨1, 0, true⟩, "r30:31", "[r11:1]"⟩

/-- The third B-window load at PC 987. -/
def load987 : TlaBlock2d :=
  ⟨"load_block2d.ugm.d16v.a64", ⟨1, 0, true⟩, "r96:16", "[r7:1]"⟩

/-- The fourth B-window load at PC 990. -/
def load990 : TlaBlock2d :=
  ⟨"load_block2d.ugm.d16v.a64", ⟨1, 0, true⟩, "r112:16", "[r7:1]"⟩

set_option maxRecDepth 100000 in
theorem parseLoad979 : (progInstrAt 979).bind parseTlaBlock2dPlain = some load979 := by
  decide

set_option maxRecDepth 100000 in
theorem parseLoad983 : (progInstrAt 983).bind parseTlaBlock2dPlain = some load983 := by
  decide

set_option maxRecDepth 100000 in
theorem parseLoad986 : (progInstrAt 986).bind parseTlaBlock2dPlain = some load986 := by
  decide

set_option maxRecDepth 100000 in
theorem parseLoad987 : (progInstrAt 987).bind parseTlaBlock2dPlain = some load987 := by
  decide

set_option maxRecDepth 100000 in
theorem parseLoad990 : (progInstrAt 990).bind parseTlaBlock2dPlain = some load990 := by
  decide

/-- PC 979 feeds the `r64` B tile. -/
theorem load979_feeds_readTileB (st : TlaState) (mem : TlaMem) (bti : Nat → Word)
    (p : TlaState × TlaMem) (h : tlaBlock2dLoadW? st mem bti ⟨64, 16⟩ load979 = some p)
    (a : TlaAddr) (hp : parseTlaAddr load979.addr = some a)
    (k n : Nat) (hk : k < 16) (hn : n < 8)
    (ha : load979.exec.elementActive (bLane n k) = true) :
    readTileB (flat p.1.regs) 64 0 k n =
      mem.loadTile (a.effAddr st bti) (bLane n k) :=
  loadWindow_feeds_readTileB st mem bti load979 64 p h a hp k n hk hn ha

/-- PC 983 feeds the `r80` B tile. -/
theorem load983_feeds_readTileB (st : TlaState) (mem : TlaMem) (bti : Nat → Word)
    (p : TlaState × TlaMem) (h : tlaBlock2dLoadW? st mem bti ⟨80, 16⟩ load983 = some p)
    (a : TlaAddr) (hp : parseTlaAddr load983.addr = some a)
    (k n : Nat) (hk : k < 16) (hn : n < 8)
    (ha : load983.exec.elementActive (bLane n k) = true) :
    readTileB (flat p.1.regs) 80 0 k n =
      mem.loadTile (a.effAddr st bti) (bLane n k) :=
  loadWindow_feeds_readTileB st mem bti load983 80 p h a hp k n hk hn ha

/-- PC 986 feeds the `r30` A tile. -/
theorem load986_feeds_readTileA (st : TlaState) (mem : TlaMem) (bti : Nat → Word)
    (p : TlaState × TlaMem) (h : tlaBlock2dLoadW? st mem bti ⟨30, 31⟩ load986 = some p)
    (a : TlaAddr) (hp : parseTlaAddr load986.addr = some a)
    (m k : Nat) (hm : m < 8) (hk : k < 16)
    (ha : load986.exec.elementActive (aLane m k) = true) :
    readTileA p.1.regs 30 m k =
      mem.loadTile (a.effAddr st bti) (aLane m k) :=
  loadWindow_feeds_readTileA st mem bti load986 30 p h a hp m k hm hk ha

/-- PC 987 feeds the `r96` B tile. -/
theorem load987_feeds_readTileB (st : TlaState) (mem : TlaMem) (bti : Nat → Word)
    (p : TlaState × TlaMem) (h : tlaBlock2dLoadW? st mem bti ⟨96, 16⟩ load987 = some p)
    (a : TlaAddr) (hp : parseTlaAddr load987.addr = some a)
    (k n : Nat) (hk : k < 16) (hn : n < 8)
    (ha : load987.exec.elementActive (bLane n k) = true) :
    readTileB (flat p.1.regs) 96 0 k n =
      mem.loadTile (a.effAddr st bti) (bLane n k) :=
  loadWindow_feeds_readTileB st mem bti load987 96 p h a hp k n hk hn ha

/-- PC 990 feeds the `r112` B tile. -/
theorem load990_feeds_readTileB (st : TlaState) (mem : TlaMem) (bti : Nat → Word)
    (p : TlaState × TlaMem) (h : tlaBlock2dLoadW? st mem bti ⟨112, 16⟩ load990 = some p)
    (a : TlaAddr) (hp : parseTlaAddr load990.addr = some a)
    (k n : Nat) (hk : k < 16) (hn : n < 8)
    (ha : load990.exec.elementActive (bLane n k) = true) :
    readTileB (flat p.1.regs) 112 0 k n =
      mem.loadTile (a.effAddr st bti) (bLane n k) :=
  loadWindow_feeds_readTileB st mem bti load990 112 p h a hp k n hk hn ha

end IntelGpu
