-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaAccumulatorStore
public import Intel.TlaPlain

@[expose] public section

/-!
# The second accumulator block's output store

The mainloop's four accumulator stores write only `r21..r28`. The second
accumulator block `r13..r20` leaves the kernel through the epilogue's plain
`store_block2d.ugm.d32.a64 [r4:1], r13:8` at PC 2116.

This module proves the window-store bridge for `r13:8` and composes it with
`mainloopDpasRun_acc1_sum`: the stored element is the initial `r13` tile
element plus the ordered sum of the 32 DPAS slabs.
-/

namespace IntelGpu

theorem laneReg_13 (row col : Nat) (hc : col < 8) :
    (⟨13, 8⟩ : TlaWindow).laneReg (row * 8 + col) = 13 + row := by
  unfold TlaWindow.laneReg
  rw [Nat.mul_comm row 8, Nat.mul_add_div (by decide), Nat.div_eq_of_lt hc, Nat.add_zero]

theorem laneElem_13 (row col : Nat) (hc : col < 8) :
    (⟨13, 8⟩ : TlaWindow).laneElem (row * 8 + col) = col := by
  unfold TlaWindow.laneElem
  rw [Nat.mul_comm row 8, Nat.mul_add_mod, Nat.mod_eq_of_lt hc]

/-- A store through `r13:8` writes `readTileC st.regs 13`. -/
theorem store13_readTileC (st : TlaState) (mem : TlaMem) (bti : Nat → Word)
    (b : TlaBlock2d) (p : TlaState × TlaMem)
    (h : tlaBlock2dStoreW? st mem bti ⟨13, 8⟩ b = some p)
    (a : TlaAddr) (hp : parseTlaAddr b.addr = some a)
    (row col : Nat) (_hr : row < 8) (hc : col < 8)
    (ha : b.exec.elementActive (row * 8 + col) = true) :
    p.2.loadTile (a.effAddr st bti) (row * 8 + col) = readTileC st.regs 13 row col := by
  have hw := tlaBlock2dStoreW?_lane st mem bti ⟨13, 8⟩ b p h a hp (row * 8 + col)
  rw [laneReg_13 row col hc, laneElem_13 row col hc] at hw
  rw [hw, ite_eq_left ha]
  unfold readTileC
  rfl

/-- The epilogue store at PC 2116. -/
def store2116 : TlaBlock2d :=
  ⟨"store_block2d.ugm.d32.a64", ⟨1, 0, true⟩, "r13:8", "[r4:1]"⟩

set_option maxRecDepth 100000 in
theorem parseStore2116 :
    (progInstrAt 2116).bind parseTlaBlock2dPlainStore = some store2116 := by
  decide

set_option maxRecDepth 10000000 in
/-- The epilogue store writes the accumulated `r13` tile: the initial element
plus the ordered slab sum of the final DPAS phase. -/
theorem store2116_dpas_sum (st : TlaState) (mem : TlaMem) (bti : Nat → Word)
    (p : TlaState × TlaMem)
    (h : tlaBlock2dStoreW? (dpasState st) mem bti ⟨13, 8⟩ store2116 = some p)
    (a : TlaAddr) (hp : parseTlaAddr store2116.addr = some a)
    (row col : Nat) (hr : row < 8) (hc : col < 8)
    (ha : store2116.exec.elementActive (row * 8 + col) = true) :
    p.2.loadTile (a.effAddr (dpasState st) bti) (row * 8 + col) =
      readTileC st.regs 13 row col +
        (realTlaGemmDpas.map (fun d =>
          dpasSlab 16 (readTileA st.regs d.srcA) (readTileB st.regs d.srcB 0)
            row col)).sum := by
  rw [store13_readTileC (dpasState st) mem bti store2116 p h a hp row col hr hc ha]
  rw [show (dpasState st).regs = mainloopDpasRun st.regs from rfl]
  exact mainloopDpasRun_acc1_sum st.regs row col (by omega) (by omega)

end IntelGpu
