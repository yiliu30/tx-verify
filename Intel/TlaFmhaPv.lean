-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaFmhaDpas
public import Intel.TlaDpasFold
public import Intel.Mainloop

@[expose] public section

/-!
# The PV DPAS chain

The 32 PV atoms accumulate into `r74..r194` while their A/B sources sit at
`r202..r246`, above every PV accumulator. For a fixed accumulator, the reads
are therefore stable across the whole chain and the fold is the initial block
plus the ordered slab sum (`fmhaAtomRun_fixed_acc`). The first PV group
(`r74`) is worked out concretely.
-/

namespace IntelGpu

/-- Fold a list of atoms. -/
def fmhaAtomRun (steps : List FmhaDpas) (rf : RegFile) : RegFile :=
  steps.foldl fmhaAtomStep rf

theorem readTileA_fmhaAtomStep_above (rf : RegFile) (d : FmhaDpas)
    (readBase m k : Nat) (h : d.acc0 + 8 ≤ readBase + k) :
    readTileA (fmhaAtomStep rf d) readBase m k = readTileA rf readBase m k := by
  unfold fmhaAtomStep
  exact readTileA_writeTileC_above rf _ readBase d.acc0 m k h

theorem readTileB_fmhaAtomStep_above (rf : RegFile) (d : FmhaDpas)
    (readBase sub k n : Nat) (h : d.acc0 + 8 ≤ readBase + n) :
    readTileB (fmhaAtomStep rf d) readBase sub k n = readTileB rf readBase sub k n := by
  unfold fmhaAtomStep
  exact readTileB_writeTileC_above rf _ readBase sub d.acc0 k n h

theorem readTileA_fmhaAtomStep_below (rf : RegFile) (d : FmhaDpas)
    (readBase m k : Nat) (h : readBase + k < d.acc0) :
    readTileA (fmhaAtomStep rf d) readBase m k = readTileA rf readBase m k := by
  unfold fmhaAtomStep
  exact readTileA_writeTileC_below rf _ readBase d.acc0 m k h

theorem readTileB_fmhaAtomStep_below (rf : RegFile) (d : FmhaDpas)
    (readBase sub k n : Nat) (h : readBase + n < d.acc0) :
    readTileB (fmhaAtomStep rf d) readBase sub k n = readTileB rf readBase sub k n := by
  unfold fmhaAtomStep
  exact readTileB_writeTileC_below rf _ readBase sub d.acc0 k n h

/-- A fixed-accumulator chain is the initial block plus the ordered slab sum.
Each source is either entirely above the accumulator or entirely below it, so
the reads are stable across the chain. -/
theorem fmhaAtomRun_fixed_acc (steps : List FmhaDpas) (rf : RegFile) (acc : Nat)
    (hacc : ∀ d, d ∈ steps → d.acc0 = acc)
    (hA : ∀ d, d ∈ steps → acc + 8 ≤ d.srcA ∨ d.srcA + 8 ≤ acc)
    (hB : ∀ d, d ∈ steps → acc + 8 ≤ d.srcB ∨ d.srcB + 8 ≤ acc) :
    ∀ m n, m < 8 → n < 8 →
      readTileC (fmhaAtomRun steps rf) acc m n =
        readTileC rf acc m n +
          (steps.map (fun d =>
            dpasSlab 16 (readTileA rf d.srcA) (readTileB rf d.srcB 0) m n)).sum := by
  induction steps generalizing rf with
  | nil => intro m n _ _; simp [fmhaAtomRun]
  | cons d ds ih =>
      intro m n hm hn
      simp only [fmhaAtomRun, List.foldl_cons]
      have hd : d.acc0 = acc := hacc d (by simp)
      have hstep : readTileC (fmhaAtomStep rf d) acc m n =
          readTileC rf acc m n + dpasSlab 16 (readTileA rf d.srcA) (readTileB rf d.srcB 0) m n := by
        simpa [hd, tlaSlab] using fmhaAtomStep_acc0 rf d m n hm hn
      change readTileC (fmhaAtomRun ds (fmhaAtomStep rf d)) acc m n = _
      rw [ih (fmhaAtomStep rf d)
        (fun e he => hacc e (by simp [he]))
        (fun e he => hA e (by simp [he]))
        (fun e he => hB e (by simp [he])) m n hm hn]
      have hmap : ds.map (fun e =>
            dpasSlab 16 (readTileA (fmhaAtomStep rf d) e.srcA)
              (readTileB (fmhaAtomStep rf d) e.srcB 0) m n) =
          ds.map (fun e =>
            dpasSlab 16 (readTileA rf e.srcA) (readTileB rf e.srcB 0) m n) := by
        apply List.map_congr_left
        intro e he
        exact dpasSlab_congr 16 _ _ _ _ m n
          (fun k _ => by
            rcases hA e (by simp [he]) with h | h
            · exact readTileA_fmhaAtomStep_above rf d e.srcA k m (by omega)
            · exact readTileA_fmhaAtomStep_below rf d e.srcA k m (by omega))
          (fun k _ => by
            rcases hB e (by simp [he]) with h | h
            · exact readTileB_fmhaAtomStep_above rf d e.srcB 0 k n (by omega)
            · exact readTileB_fmhaAtomStep_below rf d e.srcB 0 k n (by omega))
      rw [hmap, hstep]
      simp [List.sum_cons, BitVec.add_assoc]

set_option maxRecDepth 1000000 in
/-- Every PV source is below its group accumulator (`src + 8 <= 74` suffices
for the first group; the check below is at the highest PV accumulator `194`). -/
theorem pvDpas_sources_below :
    pvDpas.all (fun d => d.srcA + 8 ≤ 194 && d.srcB + 8 ≤ 194) = true := by decide

/-- The first PV accumulator group. -/
def pv74 : List FmhaDpas := pvDpas.filter (fun d => d.acc0 = 74)

set_option maxRecDepth 1000000 in
theorem pv74_length : pv74.length = 2 := by decide

set_option maxRecDepth 1000000 in
theorem pv74_sources : pv74.all (fun d => d.srcA + 8 ≤ 74 && d.srcB + 8 ≤ 74) = true := by
  decide

/-- The two atoms into `r74` sum their slabs. -/
theorem pv74_sum (rf : RegFile) (m n : Nat) (hm : m < 8) (hn : n < 8) :
    readTileC (fmhaAtomRun pv74 rf) 74 m n =
      readTileC rf 74 m n +
        (pv74.map (fun d =>
          dpasSlab 16 (readTileA rf d.srcA) (readTileB rf d.srcB 0) m n)).sum := by
  refine fmhaAtomRun_fixed_acc pv74 rf 74 ?_ ?_ ?_ m n hm hn
  · intro d hd
    have h := (List.mem_filter.mp hd).2
    simpa using h
  · intro d hd
    have h := (List.all_eq_true.mp pv74_sources) d hd
    simp only [Bool.and_eq_true] at h
    exact Or.inr (of_decide_eq_true h.1)
  · intro d hd
    have h := (List.all_eq_true.mp pv74_sources) d hd
    simp only [Bool.and_eq_true] at h
    exact Or.inr (of_decide_eq_true h.2)

end IntelGpu
