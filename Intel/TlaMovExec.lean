-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaMovDecode
public import Intel.FmhaExec
public import Intel.RealSemantics

@[expose] public section

/-!
# Executing the predicated SYCL-TLA moves

`Intel/TlaMovDecode` turns the 377 `(W) mov` statements into
`exec`/`dst`/`src`. This module executes one move on the logical register file
`RegFile`. A register destination writes the active lanes of the destination
region; `null` is a no-op; an immediate source is embedded as a signed 32-bit
word. The two prologue moves are worked out, and the frame law shows that only
the destination register changes.
-/

namespace IntelGpu

/-- Read a TLA source operand at a lane. -/
def readTlaSrc (rf : RegFile) : TlaSrc → Nat → Word
  | .reg g => fun i => rf g.num (srcIndex g i)
  | .cr _ _ => fun _ => 0
  | .imm v _ => fun _ => BitVec.ofInt 32 v

/-- Write the active destination elements of a TLA move. -/
def writeTlaMasked (rf : RegFile) (g : Grf) (e : Exec) (f : Nat → Word) : RegFile :=
  fun r j =>
    if r = g.num then
      let b := g.row * 8 + g.col
      let k := j - b
      if g.hstride = 1 ∧ b ≤ j then
        let i := k
        let l := if e.noMask then i else e.offset + i
        if e.laneActive l then f i else rf r j
      else if g.hstride = 2 ∧ b ≤ j ∧ k % 2 = 0 then
        let i := k / 2
        let l := if e.noMask then i else e.offset + i
        if e.laneActive l then f i else rf r j
      else rf r j
    else rf r j

/-- Execute one predicated move. -/
def tlaMovStep (rf : RegFile) (m : TlaMov) : RegFile :=
  match m.dst with
  | .null => rf
  | .reg g => writeTlaMasked rf g m.exec (readTlaSrc rf m.src)

/-- A `null` destination leaves the register file unchanged. -/
theorem tlaMovStep_null (rf : RegFile) (e : Exec) (s : TlaSrc) :
    tlaMovStep rf ⟨e, .null, s⟩ = rf := rfl

/-- A move to a different register leaves the frame unchanged. -/
theorem tlaMovStep_frame (rf : RegFile) (e : Exec) (g : Grf) (s : TlaSrc)
    (r j : Nat) (h : r ≠ g.num) :
    tlaMovStep rf ⟨e, .reg g, s⟩ r j = rf r j := by
  unfold tlaMovStep writeTlaMasked
  simp [h]

/-- An active unit-stride destination element receives the source value. -/
theorem tlaMovStep_active (rf : RegFile) (e : Exec) (g : Grf) (s : TlaSrc)
    (j : Nat) (hb : g.row * 8 + g.col ≤ j) (hd : g.hstride = 1)
    (ha : e.laneActive (if e.noMask then j - (g.row * 8 + g.col)
      else e.offset + (j - (g.row * 8 + g.col))) = true) :
    tlaMovStep rf ⟨e, .reg g, s⟩ g.num j =
      readTlaSrc rf s (j - (g.row * 8 + g.col)) := by
  unfold tlaMovStep writeTlaMasked
  simp [hd, hb, ha]

/-- The per-thread prologue move: `r127.0 = 0` for the first 16 elements. -/
theorem prologue_zero (rf : RegFile) (j : Nat) (hj : j < 16) :
    tlaMovStep rf ⟨⟨16, 0, true⟩, .reg ⟨127, 0, 0, 1, 1, 1⟩, .imm 0 .ud⟩ 127 j = 0 := by
  have hb : (⟨127, 0, 0, 1, 1, 1⟩ : Grf).row * 8 +
      (⟨127, 0, 0, 1, 1, 1⟩ : Grf).col ≤ j := by simp
  have ha : (⟨16, 0, true⟩ : Exec).laneActive
      (if (⟨16, 0, true⟩ : Exec).noMask = true then
        j - ((⟨127, 0, 0, 1, 1, 1⟩ : Grf).row * 8 + (⟨127, 0, 0, 1, 1, 1⟩ : Grf).col)
      else (⟨16, 0, true⟩ : Exec).offset +
        (j - ((⟨127, 0, 0, 1, 1, 1⟩ : Grf).row * 8 + (⟨127, 0, 0, 1, 1, 1⟩ : Grf).col))) = true := by
    simp [Exec.laneActive, hj]
  rw [tlaMovStep_active rf ⟨16, 0, true⟩ ⟨127, 0, 0, 1, 1, 1⟩ (.imm 0 .ud) j hb rfl ha]
  simp [readTlaSrc]

/-- The id move: `r2.0 = r1.0` for the first 8 elements. -/
theorem id_move (rf : RegFile) (j : Nat) (hj : j < 8) :
    tlaMovStep rf ⟨⟨8, 0, true⟩, .reg ⟨2, 0, 0, 1, 1, 1⟩,
      .reg ⟨1, 0, 0, 1, 1, 0⟩⟩ 2 j = rf 1 j := by
  have hb : (⟨2, 0, 0, 1, 1, 1⟩ : Grf).row * 8 +
      (⟨2, 0, 0, 1, 1, 1⟩ : Grf).col ≤ j := by simp
  have ha : (⟨8, 0, true⟩ : Exec).laneActive
      (if (⟨8, 0, true⟩ : Exec).noMask = true then
        j - ((⟨2, 0, 0, 1, 1, 1⟩ : Grf).row * 8 + (⟨2, 0, 0, 1, 1, 1⟩ : Grf).col)
      else (⟨8, 0, true⟩ : Exec).offset +
        (j - ((⟨2, 0, 0, 1, 1, 1⟩ : Grf).row * 8 + (⟨2, 0, 0, 1, 1, 1⟩ : Grf).col))) = true := by
    simp [Exec.laneActive, hj]
  rw [tlaMovStep_active rf ⟨8, 0, true⟩ ⟨2, 0, 0, 1, 1, 1⟩
    (.reg ⟨1, 0, 0, 1, 1, 0⟩) j hb rfl ha]
  simp [readTlaSrc, srcIndex]

end IntelGpu
