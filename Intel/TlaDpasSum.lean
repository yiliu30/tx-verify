-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaDpasExec
public import Intel.TlaDpasFold

@[expose] public section

/-!
# The SYCL-TLA DPAS chain as an ordered sum

This module states the full 32-step accumulation with a first-order
`List.sum` accumulator. The accumulator blocks `r13..r20` and `r21..r28` are
disjoint from every source read (`r29` and above), so each step leaves later
sources unchanged. The main theorem therefore says the first accumulator is
the initial block plus the sum of the per-instruction slabs, each read from
the initial register file.
-/

namespace IntelGpu

/-- The structural run. -/
def tlaDpasRunSeq : List TlaDpas → RegFile → RegFile
  | [], rf => rf
  | d :: ds, rf => tlaDpasRunSeq ds (tlaDpasStepOf d rf)

theorem tlaDpasRunSeq_eq (steps : List TlaDpas) (rf : RegFile) :
    tlaDpasRunSeq steps rf = tlaDpasRun steps rf := by
  induction steps generalizing rf with
  | nil => rfl
  | cons d ds ih =>
      simp only [tlaDpasRunSeq, tlaDpasRun, List.foldl_cons]
      exact ih (tlaDpasStepOf d rf)

/-- The first accumulator block after one decoded step. -/
theorem tlaDpasStepOf_acc0 (d : TlaDpas) (rf : RegFile)
    (h0 : d.acc0 = 21) (h1 : d.acc1 = 13) (m n : Nat) (hm : m < 8) (hn : n < 8) :
    readTileC (tlaDpasStepOf d rf) 21 m n =
      readTileC rf 21 m n +
        dpasSlab 16 (readTileA rf d.srcA) (readTileB rf d.srcB 0) m n := by
  simp only [tlaDpasStepOf, h0, h1]
  rw [tlaDpasStep_acc0 _ _ _ _ _ tileCDisjoint_21_13 m n hm hn]
  simp only [tlaSlab]

/-- A source read above the accumulator blocks is unchanged by one decoded
step. -/
theorem readTileA_tlaDpasStepOf (d : TlaDpas) (rf : RegFile)
    (h0 : d.acc0 = 21) (h1 : d.acc1 = 13) (base : Nat) (h : 29 ≤ base) :
    readTileA (tlaDpasStepOf d rf) base = readTileA rf base := by
  simp only [tlaDpasStepOf, h0, h1]
  exact readTileA_tlaDpasStep_fun rf d.srcB d.srcA base h

/-- The same for the B source. -/
theorem readTileB_tlaDpasStepOf (d : TlaDpas) (rf : RegFile)
    (h0 : d.acc0 = 21) (h1 : d.acc1 = 13) (base sub : Nat) (h : 29 ≤ base) :
    readTileB (tlaDpasStepOf d rf) base sub = readTileB rf base sub := by
  simp only [tlaDpasStepOf, h0, h1]
  exact readTileB_tlaDpasStep_fun rf d.srcB d.srcA base sub h

set_option maxHeartbeats 2000000 in
/-- The first accumulator after the run is the initial block plus the ordered
slab sum. -/
theorem tlaDpasRunSeq_acc0_sum (steps : List TlaDpas) (rf : RegFile)
    (hacc : ∀ d, d ∈ steps → d.acc0 = 21 ∧ d.acc1 = 13)
    (hA : ∀ d, d ∈ steps → 29 ≤ d.srcA)
    (hB : ∀ d, d ∈ steps → 29 ≤ d.srcB) :
    ∀ m n, m < 8 → n < 8 →
      readTileC (tlaDpasRunSeq steps rf) 21 m n =
        readTileC rf 21 m n +
          (steps.map (fun d =>
            dpasSlab 16 (readTileA rf d.srcA) (readTileB rf d.srcB 0) m n)).sum := by
  induction steps generalizing rf with
  | nil => intro m n _ _; simp [tlaDpasRunSeq]
  | cons d ds ih =>
      intro m n hm hn
      have hd : d.acc0 = 21 ∧ d.acc1 = 13 := hacc d (by simp)
      have hstep := tlaDpasStepOf_acc0 d rf hd.1 hd.2 m n hm hn
      have hmap : ds.map (fun e =>
          dpasSlab 16 (readTileA (tlaDpasStepOf d rf) e.srcA)
            (readTileB (tlaDpasStepOf d rf) e.srcB 0) m n) =
          ds.map (fun e =>
            dpasSlab 16 (readTileA rf e.srcA) (readTileB rf e.srcB 0) m n) := by
        apply List.map_congr_left
        intro e he
        rw [readTileA_tlaDpasStepOf d rf hd.1 hd.2 e.srcA (hA e (by simp [he]))]
        rw [readTileB_tlaDpasStepOf d rf hd.1 hd.2 e.srcB 0 (hB e (by simp [he]))]
      simp only [tlaDpasRunSeq]
      rw [ih (tlaDpasStepOf d rf)
        (fun e he => hacc e (by simp [he]))
        (fun e he => hA e (by simp [he]))
        (fun e he => hB e (by simp [he])) m n hm hn]
      rw [hstep, hmap]
      simp [List.sum_cons, BitVec.add_assoc]

/-- The same statement for `tlaDpasRun`. -/
theorem tlaDpasRun_acc0_sum (steps : List TlaDpas) (rf : RegFile)
    (hacc : ∀ d, d ∈ steps → d.acc0 = 21 ∧ d.acc1 = 13)
    (hA : ∀ d, d ∈ steps → 29 ≤ d.srcA)
    (hB : ∀ d, d ∈ steps → 29 ≤ d.srcB) :
    ∀ m n, m < 8 → n < 8 →
      readTileC (tlaDpasRun steps rf) 21 m n =
        readTileC rf 21 m n +
          (steps.map (fun d =>
            dpasSlab 16 (readTileA rf d.srcA) (readTileB rf d.srcB 0) m n)).sum := by
  intro m n hm hn
  rw [← tlaDpasRunSeq_eq]
  exact tlaDpasRunSeq_acc0_sum steps rf hacc hA hB m n hm hn

set_option maxRecDepth 100000 in
/-- Every real DPAS source A base is at least `r29`. -/
theorem realTlaGemmDpas_srcA_ge :
    realTlaGemmDpas.all (fun d => 29 ≤ d.srcA) = true := by decide

set_option maxRecDepth 100000 in
/-- Every real DPAS source B base is at least `r29`. -/
theorem realTlaGemmDpas_srcB_ge :
    realTlaGemmDpas.all (fun d => 29 ≤ d.srcB) = true := by decide

/-- The full 32-step SYCL-TLA chain: the first accumulator is the initial
block plus the ordered slab sum. -/
theorem realTlaGemmDpas_acc0_sum (rf : RegFile) (m n : Nat) (hm : m < 8) (hn : n < 8) :
    readTileC (tlaDpasRun realTlaGemmDpas rf) 21 m n =
      readTileC rf 21 m n +
        (realTlaGemmDpas.map (fun d =>
          dpasSlab 16 (readTileA rf d.srcA) (readTileB rf d.srcB 0) m n)).sum := by
  apply tlaDpasRun_acc0_sum
  · intro d hd
    have h := (List.all_eq_true.mp realTlaGemmDpas_accs) d hd
    simpa [Bool.and_eq_true] using h
  · intro d hd
    exact of_decide_eq_true ((List.all_eq_true.mp realTlaGemmDpas_srcA_ge) d hd)
  · intro d hd
    exact of_decide_eq_true ((List.all_eq_true.mp realTlaGemmDpas_srcB_ge) d hd)
  · exact hm
  · exact hn

/-- The second accumulator block after one decoded step. -/
theorem tlaDpasStepOf_acc1 (d : TlaDpas) (rf : RegFile)
    (h0 : d.acc0 = 21) (h1 : d.acc1 = 13) (m n : Nat) (hm : m < 8) (hn : n < 8) :
    readTileC (tlaDpasStepOf d rf) 13 m n =
      readTileC rf 13 m n +
        dpasSlab 16 (readTileA rf d.srcA) (readTileB rf d.srcB 0) m n := by
  simp only [tlaDpasStepOf, h0, h1]
  rw [tlaDpasStep_acc1 _ _ _ _ _ m n hm hn]
  simp only [tlaSlab]

set_option maxHeartbeats 2000000 in
/-- The second accumulator after the run is the initial block plus the ordered
slab sum. -/
theorem tlaDpasRunSeq_acc1_sum (steps : List TlaDpas) (rf : RegFile)
    (hacc : ∀ d, d ∈ steps → d.acc0 = 21 ∧ d.acc1 = 13)
    (hA : ∀ d, d ∈ steps → 29 ≤ d.srcA)
    (hB : ∀ d, d ∈ steps → 29 ≤ d.srcB) :
    ∀ m n, m < 8 → n < 8 →
      readTileC (tlaDpasRunSeq steps rf) 13 m n =
        readTileC rf 13 m n +
          (steps.map (fun d =>
            dpasSlab 16 (readTileA rf d.srcA) (readTileB rf d.srcB 0) m n)).sum := by
  induction steps generalizing rf with
  | nil => intro m n _ _; simp [tlaDpasRunSeq]
  | cons d ds ih =>
      intro m n hm hn
      have hd : d.acc0 = 21 ∧ d.acc1 = 13 := hacc d (by simp)
      have hstep := tlaDpasStepOf_acc1 d rf hd.1 hd.2 m n hm hn
      have hmap : ds.map (fun e =>
          dpasSlab 16 (readTileA (tlaDpasStepOf d rf) e.srcA)
            (readTileB (tlaDpasStepOf d rf) e.srcB 0) m n) =
          ds.map (fun e =>
            dpasSlab 16 (readTileA rf e.srcA) (readTileB rf e.srcB 0) m n) := by
        apply List.map_congr_left
        intro e he
        rw [readTileA_tlaDpasStepOf d rf hd.1 hd.2 e.srcA (hA e (by simp [he]))]
        rw [readTileB_tlaDpasStepOf d rf hd.1 hd.2 e.srcB 0 (hB e (by simp [he]))]
      simp only [tlaDpasRunSeq]
      rw [ih (tlaDpasStepOf d rf)
        (fun e he => hacc e (by simp [he]))
        (fun e he => hA e (by simp [he]))
        (fun e he => hB e (by simp [he])) m n hm hn]
      rw [hstep, hmap]
      simp [List.sum_cons, BitVec.add_assoc]

/-- The same statement for `tlaDpasRun`. -/
theorem tlaDpasRun_acc1_sum (steps : List TlaDpas) (rf : RegFile)
    (hacc : ∀ d, d ∈ steps → d.acc0 = 21 ∧ d.acc1 = 13)
    (hA : ∀ d, d ∈ steps → 29 ≤ d.srcA)
    (hB : ∀ d, d ∈ steps → 29 ≤ d.srcB) :
    ∀ m n, m < 8 → n < 8 →
      readTileC (tlaDpasRun steps rf) 13 m n =
        readTileC rf 13 m n +
          (steps.map (fun d =>
            dpasSlab 16 (readTileA rf d.srcA) (readTileB rf d.srcB 0) m n)).sum := by
  intro m n hm hn
  rw [← tlaDpasRunSeq_eq]
  exact tlaDpasRunSeq_acc1_sum steps rf hacc hA hB m n hm hn

/-- The full 32-step chain for the second accumulator. -/
theorem realTlaGemmDpas_acc1_sum (rf : RegFile) (m n : Nat) (hm : m < 8) (hn : n < 8) :
    readTileC (tlaDpasRun realTlaGemmDpas rf) 13 m n =
      readTileC rf 13 m n +
        (realTlaGemmDpas.map (fun d =>
          dpasSlab 16 (readTileA rf d.srcA) (readTileB rf d.srcB 0) m n)).sum := by
  apply tlaDpasRun_acc1_sum
  · intro d hd
    have h := (List.all_eq_true.mp realTlaGemmDpas_accs) d hd
    simpa [Bool.and_eq_true] using h
  · intro d hd
    exact of_decide_eq_true ((List.all_eq_true.mp realTlaGemmDpas_srcA_ge) d hd)
  · intro d hd
    exact of_decide_eq_true ((List.all_eq_true.mp realTlaGemmDpas_srcB_ge) d hd)
  · exact hm
  · exact hn

end IntelGpu
