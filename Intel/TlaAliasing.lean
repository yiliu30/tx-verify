-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaWindow

@[expose] public section

/-!
# Aliasing laws for the TLA memory and windows

The tile memory is a function of the effective base address, so aliasing is
word equality: two tiles alias exactly when their `Word` addresses are equal.
This module proves the store-store laws (`same` and `commute`), the
address-aliasing characterization, and the window aliasing law: when one
window writes a physical register element and a second window writes the same
element, the second write wins; when the second is inactive the first value
survives.
-/

namespace IntelGpu

/-- Tile addresses alias exactly when the words are equal. -/
theorem tileAddr_eq_of_toNat_eq (a b : Word) (h : a.toNat = b.toNat) : a = b :=
  BitVec.toNat_inj.mp h

theorem tileAddr_toNat_eq_of_eq (a b : Word) (h : a = b) : a.toNat = b.toNat := by
  rw [h]

/-- A second store to the same tile replaces the first. -/
theorem storeTile_storeTile_same (m : TlaMem) (ea : Word) (f g : Nat → Word) :
    (m.storeTile ea f).storeTile ea g = m.storeTile ea g := by
  cases m with
  | mk cells =>
      simp only [TlaMem.storeTile]
      congr 1
      funext b l
      by_cases h : b = ea.toNat <;> simp [h]

/-- Stores to different tiles commute. -/
theorem storeTile_storeTile_other (m : TlaMem) (ea ea' : Word) (f g : Nat → Word)
    (h : ea ≠ ea') :
    (m.storeTile ea f).storeTile ea' g = (m.storeTile ea' g).storeTile ea f := by
  cases m with
  | mk cells =>
      have hne : ea.toNat ≠ ea'.toNat := fun hc => h (tileAddr_eq_of_toNat_eq _ _ hc)
      simp only [TlaMem.storeTile]
      congr 1
      funext b l
      by_cases h1 : b = ea.toNat
      · subst h1
        simp [hne]
      · by_cases h2 : b = ea'.toNat
        · subst h2
          simp [h1, hne]
        · simp [h1, h2]

/-- A window write at an in-window element. -/
theorem writeWindow_some (rf : RegFile) (w : TlaWindow) (e : Exec)
    (f : Nat → Word) (r j i : Nat) (hi : w.index r j = some i) :
    writeWindow rf w e f r j = if e.elementActive i then f i else rf r j := by
  simp [writeWindow, hi]

/-- A window write to a physical element that a second window also covers:
the second write wins when active. -/
theorem writeWindow_writeWindow_share (rf : RegFile) (w1 w2 : TlaWindow)
    (e1 e2 : Exec) (f1 f2 : Nat → Word) (r j i l : Nat)
    (_h1 : w1.index r j = some i) (h2 : w2.index r j = some l)
    (ha : e2.elementActive l = true) :
    writeWindow (writeWindow rf w1 e1 f1) w2 e2 f2 r j = f2 l :=
  writeWindow_active (writeWindow rf w1 e1 f1) w2 e2 f2 r j l h2 ha

/-- The same aliased element when the second window is inactive: the first
window's value survives. -/
theorem writeWindow_writeWindow_share_inactive (rf : RegFile) (w1 w2 : TlaWindow)
    (e1 e2 : Exec) (f1 f2 : Nat → Word) (r j i l : Nat)
    (h1 : w1.index r j = some i) (h2 : w2.index r j = some l)
    (ha : e2.elementActive l = false) :
    writeWindow (writeWindow rf w1 e1 f1) w2 e2 f2 r j =
      if e1.elementActive i then f1 i else rf r j := by
  rw [writeWindow_inactive _ w2 e2 f2 r j l h2 ha, writeWindow_some rf w1 e1 f1 r j i h1]

/-- An element outside a window is invisible to that window's writes. -/
theorem writeWindow_frame_alias (rf : RegFile) (w : TlaWindow) (e : Exec)
    (f : Nat → Word) (r j : Nat) (h : w.index r j = none) :
    writeWindow rf w e f r j = rf r j :=
  writeWindow_frame rf w e f r j h

end IntelGpu
