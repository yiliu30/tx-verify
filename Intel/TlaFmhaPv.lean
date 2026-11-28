-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaFmhaDpas
public import Intel.TlaDpasFold
public import Intel.Mainloop

@[expose] public section

/-!
# The PV DPAS chain (DPAS-only sub-run)

The 32 PV atoms accumulate into `r74..r194`. Each group of two atoms shares
one accumulator, and within the DPAS-only sub-run the A/B source windows are
disjoint from that accumulator, so the fold is the initial block plus the
ordered slab sum (`fmhaAtomRun_fixed_acc`).

This is a statement about a DPAS-only sub-run. The real prefill schedule
reloads A/B source registers between short DPAS groups, so composing these
chains with the load schedule is a separate, still-open step.
-/

namespace IntelGpu

/-- Fold a list of atoms. -/
def fmhaAtomRun (steps : List FmhaDpas) (rf : RegFile) : RegFile :=
  steps.foldl fmhaAtomStep rf

theorem bf16ReadA_fmhaAtomStep_above (rf : RegFile) (d : FmhaDpas)
    (readBase : Nat) (h : d.acc0 + 8 ≤ readBase) (m k : Nat) (hk : k < 8) :
    bf16ReadA (fmhaAtomStep rf d) readBase m k = bf16ReadA rf readBase m k := by
  unfold bf16ReadA fmhaAtomStep
  rw [readTileA_writeTileC_above _ _ readBase d.acc0 m k (by omega)]

theorem bf16ReadB_fmhaAtomStep_above (rf : RegFile) (d : FmhaDpas)
    (readBase : Nat) (h : d.acc0 + 8 ≤ readBase) (k n : Nat) (hn : n < 8) :
    bf16ReadB (fmhaAtomStep rf d) readBase k n = bf16ReadB rf readBase k n := by
  unfold bf16ReadB fmhaAtomStep
  rw [readTileB_writeTileC_above _ _ readBase 0 d.acc0 k n (by omega)]

theorem bf16ReadA_fmhaAtomStep_below (rf : RegFile) (d : FmhaDpas)
    (readBase : Nat) (h : readBase + 8 ≤ d.acc0) (m k : Nat) (hk : k < 8) :
    bf16ReadA (fmhaAtomStep rf d) readBase m k = bf16ReadA rf readBase m k := by
  unfold bf16ReadA fmhaAtomStep
  rw [readTileA_writeTileC_below _ _ readBase d.acc0 m k (by omega)]

theorem bf16ReadB_fmhaAtomStep_below (rf : RegFile) (d : FmhaDpas)
    (readBase : Nat) (h : readBase + 8 ≤ d.acc0) (k n : Nat) (hn : n < 8) :
    bf16ReadB (fmhaAtomStep rf d) readBase k n = bf16ReadB rf readBase k n := by
  unfold bf16ReadB fmhaAtomStep
  rw [readTileB_writeTileC_below _ _ readBase 0 d.acc0 k n (by omega)]

/-- A fixed-accumulator chain is the initial block plus the ordered BF16
slab sum. Each source is either entirely above or entirely below the
accumulator, so the reads are stable across the chain. -/
theorem fmhaAtomRun_fixed_acc (steps : List FmhaDpas) (rf : RegFile) (acc : Nat)
    (hacc : ∀ d, d ∈ steps → d.acc0 = acc)
    (hA : ∀ d, d ∈ steps → acc + 8 ≤ d.srcA ∨ d.srcA + 8 ≤ acc)
    (hB : ∀ d, d ∈ steps → acc + 8 ≤ d.srcB ∨ d.srcB + 8 ≤ acc) :
    ∀ m n, m < 8 → n < 8 →
      readTileC (fmhaAtomRun steps rf) acc m n =
        readTileC rf acc m n +
          (steps.map (fun d => fmhaBf16Slab rf d m n)).sum := by
  induction steps generalizing rf with
  | nil => intro m n _ _; simp [fmhaAtomRun]
  | cons d ds ih =>
      intro m n hm hn
      simp only [fmhaAtomRun, List.foldl_cons]
      have hd : d.acc0 = acc := hacc d (by simp)
      have hstep : readTileC (fmhaAtomStep rf d) acc m n =
          readTileC rf acc m n + fmhaBf16Slab rf d m n := by
        simpa [hd] using fmhaAtomStep_acc0 rf d m n hm hn
      change readTileC (fmhaAtomRun ds (fmhaAtomStep rf d)) acc m n = _
      rw [ih (fmhaAtomStep rf d)
        (fun e he => hacc e (by simp [he]))
        (fun e he => hA e (by simp [he]))
        (fun e he => hB e (by simp [he])) m n hm hn]
      have hmap : ds.map (fun e => fmhaBf16Slab (fmhaAtomStep rf d) e m n) =
          ds.map (fun e => fmhaBf16Slab rf e m n) := by
        apply List.map_congr_left
        intro e he
        unfold fmhaBf16Slab
        exact dpasSlab_congr 16 _ _ _ _ m n
          (fun k _ => by
            rcases hA e (by simp [he]) with h | h
            · exact bf16ReadA_fmhaAtomStep_above rf d e.srcA (by simpa [hd] using h) k m hm
            · exact bf16ReadA_fmhaAtomStep_below rf d e.srcA (by simpa [hd] using h) k m hm)
          (fun k _ => by
            rcases hB e (by simp [he]) with h | h
            · exact bf16ReadB_fmhaAtomStep_above rf d e.srcB (by simpa [hd] using h) k n hn
            · exact bf16ReadB_fmhaAtomStep_below rf d e.srcB (by simpa [hd] using h) k n hn)
      rw [hmap, hstep]
      simp [List.sum_cons, BitVec.add_assoc]

set_option maxRecDepth 1000000 in
/-- All PV sources are below the highest PV accumulator. -/
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
        (pv74.map (fun d => fmhaBf16Slab rf d m n)).sum := by
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
