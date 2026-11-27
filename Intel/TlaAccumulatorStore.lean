-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaAccumulator
public import Intel.TlaMainloopIterate

@[expose] public section

/-!
# The stored accumulator is the DPAS slab sum

After the mainloop DPAS phase, the block stores the `r21..r28` accumulator
block through `r21:4` and `r25:4` at PCs 1394 and 1395. This module composes
the window store bridge with `mainloopDpasRun_acc0_sum`: the value written to
memory lane `row*8+col` is the initial C element plus the ordered sum of the
32 DPAS slabs, for both the first and the last four rows of the block.

The second accumulator block `r13..r20` is not stored anywhere in this dump.
-/

namespace IntelGpu

set_option maxRecDepth 10000000 in
/-- The `r21:4` store writes the accumulated first four C rows. -/
theorem store21_dpas_sum (st : TlaState) (mem : TlaMem) (bti : Nat → Word)
    (b : TlaBlock2d) (p : TlaState × TlaMem)
    (h : tlaBlock2dStoreW? (dpasState st) mem bti ⟨21, 4⟩ b = some p)
    (a : TlaAddr) (hp : parseTlaAddr b.addr = some a)
    (row col : Nat) (hr : row < 4) (hc : col < 8)
    (ha : b.exec.elementActive (row * 8 + col) = true) :
    p.2.loadTile (a.effAddr (dpasState st) bti) (row * 8 + col) =
      readTileC st.regs 21 row col +
        (realTlaGemmDpas.map (fun d =>
          dpasSlab 16 (readTileA st.regs d.srcA) (readTileB st.regs d.srcB 0)
            row col)).sum := by
  rw [store21_readTileC (dpasState st) mem bti b p h a hp row col hr hc ha]
  rw [show (dpasState st).regs = mainloopDpasRun st.regs from rfl]
  exact mainloopDpasRun_acc0_sum st.regs row col (by omega) (by omega)

set_option maxRecDepth 10000000 in
/-- The `r25:4` store writes the accumulated last four C rows. -/
theorem store25_dpas_sum (st : TlaState) (mem : TlaMem) (bti : Nat → Word)
    (b : TlaBlock2d) (p : TlaState × TlaMem)
    (h : tlaBlock2dStoreW? (dpasState st) mem bti ⟨25, 4⟩ b = some p)
    (a : TlaAddr) (hp : parseTlaAddr b.addr = some a)
    (row col : Nat) (hr : 4 ≤ row) (hr' : row < 8) (hc : col < 8)
    (ha : b.exec.elementActive ((row - 4) * 8 + col) = true) :
    p.2.loadTile (a.effAddr (dpasState st) bti) ((row - 4) * 8 + col) =
      readTileC st.regs 21 row col +
        (realTlaGemmDpas.map (fun d =>
          dpasSlab 16 (readTileA st.regs d.srcA) (readTileB st.regs d.srcB 0)
            row col)).sum := by
  rw [store25_readTileC (dpasState st) mem bti b p h a hp row col hr hr' hc ha]
  rw [show (dpasState st).regs = mainloopDpasRun st.regs from rfl]
  rw [readTileC_25_eq_21 (mainloopDpasRun st.regs) row col hr hr']
  exact mainloopDpasRun_acc0_sum st.regs row col (by omega) (by omega)

end IntelGpu
