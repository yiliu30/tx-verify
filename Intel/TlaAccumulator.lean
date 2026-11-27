-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaWindow

@[expose] public section

/-!
# Bridging the accumulator windows to `readTileC`

The C tile model reads `readTileC rf base m n = rf (base + m) n`. The
accumulator windows `r21:4` and `r25:4` cover registers `21..24` and `25..28`
with lanes `m*8+n` and `(m-4)*8+n`. This module proves that a window load
writes exactly the C-tile elements and a window store reads exactly them, so
the block's accumulator loads (PCs 1385/1387) and stores (PCs 1394/1395) are
the tile load and store of the `r21..r28` C block.
-/

namespace IntelGpu

theorem laneReg_21 (m n : Nat) (hn : n < 8) :
    (⟨21, 4⟩ : TlaWindow).laneReg (m * 8 + n) = 21 + m := by
  unfold TlaWindow.laneReg
  rw [Nat.mul_comm m 8, Nat.mul_add_div (by decide), Nat.div_eq_of_lt hn, Nat.add_zero]

theorem laneElem_21 (m n : Nat) (hn : n < 8) :
    (⟨21, 4⟩ : TlaWindow).laneElem (m * 8 + n) = n := by
  unfold TlaWindow.laneElem
  rw [Nat.mul_comm m 8, Nat.mul_add_mod, Nat.mod_eq_of_lt hn]

theorem laneReg_25 (m n : Nat) (_hm : 4 ≤ m) (hn : n < 8) :
    (⟨25, 4⟩ : TlaWindow).laneReg ((m - 4) * 8 + n) = 25 + (m - 4) := by
  unfold TlaWindow.laneReg
  rw [Nat.mul_comm (m - 4) 8, Nat.mul_add_div (by decide), Nat.div_eq_of_lt hn, Nat.add_zero]

theorem laneElem_25 (m n : Nat) (hn : n < 8) :
    (⟨25, 4⟩ : TlaWindow).laneElem ((m - 4) * 8 + n) = n := by
  unfold TlaWindow.laneElem
  rw [Nat.mul_comm (m - 4) 8, Nat.mul_add_mod, Nat.mod_eq_of_lt hn]

theorem readTileC_25_eq_21 (rf : RegFile) (m n : Nat) (hm : 4 ≤ m) (hm' : m < 8) :
    readTileC rf 25 (m - 4) n = readTileC rf 21 m n := by
  unfold readTileC
  congr 1
  omega

/-- Loading `r21:4` writes the first four rows of the C tile. -/
theorem load21_readTileC (st : TlaState) (m : TlaMem) (bti : Nat → Word)
    (b : TlaBlock2d) (p : TlaState × TlaMem)
    (h : tlaBlock2dLoadW? st m bti ⟨21, 4⟩ b = some p)
    (a : TlaAddr) (hp : parseTlaAddr b.addr = some a)
    (row col : Nat) (_hr : row < 4) (hc : col < 8)
    (ha : b.exec.elementActive (row * 8 + col) = true) :
    readTileC p.1.regs 21 row col = m.loadTile (a.effAddr st bti) (row * 8 + col) := by
  have hlt : row * 8 + col < (⟨21, 4⟩ : TlaWindow).lanes := by
    show row * 8 + col < 32
    omega
  have hw := tlaBlock2dLoadW?_active st m bti ⟨21, 4⟩ b p h a hp
    (row * 8 + col) hlt ha
  rw [laneReg_21 row col hc, laneElem_21 row col hc] at hw
  unfold readTileC
  exact hw

/-- Storing `r21:4` writes the first four rows of the C tile. -/
theorem store21_readTileC (st : TlaState) (m : TlaMem) (bti : Nat → Word)
    (b : TlaBlock2d) (p : TlaState × TlaMem)
    (h : tlaBlock2dStoreW? st m bti ⟨21, 4⟩ b = some p)
    (a : TlaAddr) (hp : parseTlaAddr b.addr = some a)
    (row col : Nat) (_hr : row < 4) (hc : col < 8)
    (ha : b.exec.elementActive (row * 8 + col) = true) :
    p.2.loadTile (a.effAddr st bti) (row * 8 + col) = readTileC st.regs 21 row col := by
  have hw := tlaBlock2dStoreW?_lane st m bti ⟨21, 4⟩ b p h a hp (row * 8 + col)
  rw [laneReg_21 row col hc, laneElem_21 row col hc] at hw
  rw [hw, ite_eq_left ha]
  unfold readTileC
  rfl

/-- Loading `r25:4` writes the last four rows of the C tile. -/
theorem load25_readTileC (st : TlaState) (m : TlaMem) (bti : Nat → Word)
    (b : TlaBlock2d) (p : TlaState × TlaMem)
    (h : tlaBlock2dLoadW? st m bti ⟨25, 4⟩ b = some p)
    (a : TlaAddr) (hp : parseTlaAddr b.addr = some a)
    (row col : Nat) (hr : 4 ≤ row) (_hr' : row < 8) (hc : col < 8)
    (ha : b.exec.elementActive ((row - 4) * 8 + col) = true) :
    readTileC p.1.regs 25 (row - 4) col =
      m.loadTile (a.effAddr st bti) ((row - 4) * 8 + col) := by
  have hlt : (row - 4) * 8 + col < (⟨25, 4⟩ : TlaWindow).lanes := by
    show (row - 4) * 8 + col < 32
    omega
  have hw := tlaBlock2dLoadW?_active st m bti ⟨25, 4⟩ b p h a hp
    ((row - 4) * 8 + col) hlt ha
  rw [laneReg_25 row col hr hc, laneElem_25 row col hc] at hw
  unfold readTileC
  exact hw

/-- Storing `r25:4` writes the last four rows of the C tile. -/
theorem store25_readTileC (st : TlaState) (m : TlaMem) (bti : Nat → Word)
    (b : TlaBlock2d) (p : TlaState × TlaMem)
    (h : tlaBlock2dStoreW? st m bti ⟨25, 4⟩ b = some p)
    (a : TlaAddr) (hp : parseTlaAddr b.addr = some a)
    (row col : Nat) (hr : 4 ≤ row) (_hr' : row < 8) (hc : col < 8)
    (ha : b.exec.elementActive ((row - 4) * 8 + col) = true) :
    p.2.loadTile (a.effAddr st bti) ((row - 4) * 8 + col) =
      readTileC st.regs 25 (row - 4) col := by
  have hw := tlaBlock2dStoreW?_lane st m bti ⟨25, 4⟩ b p h a hp ((row - 4) * 8 + col)
  rw [laneReg_25 row col hr hc, laneElem_25 row col hc] at hw
  rw [hw, ite_eq_left ha]
  unfold readTileC
  rfl

end IntelGpu
