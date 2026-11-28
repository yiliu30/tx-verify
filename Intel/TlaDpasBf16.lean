-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaDpasSum
public import Intel.Bf16Pack

@[expose] public section

/-!
# The SYCL-TLA DPAS chain over BF16 sources

`Intel.TlaDpasSum` proves the accumulator sum for the raw-word DPAS step. This
module gives the BF16 numeric instantiation: each A/B source is read through
the packed BF16 halves and the `Fixed` value model, and the accumulator update
uses those decoded values. `tlaBf16Run` is the resulting chain; the main
theorems give both accumulator blocks as the initial block plus the ordered
BF16 slab sum.
-/

namespace IntelGpu

/-- The BF16 A tile read through the packed low half. -/
def bf16ReadA (rf : RegFile) (base : Nat) : Nat → Nat → Word :=
  fun m k => bf16Word (bf16Lo (readTileA rf base m k))

/-- The BF16 B tile read through the packed low half. -/
def bf16ReadB (rf : RegFile) (base : Nat) : Nat → Nat → Word :=
  fun k n => bf16Word (bf16Lo (readTileB rf base 0 k n))

/-- One BF16 DPAS slab read from `rf`. -/
def tlaBf16Slab (rf : RegFile) (d : TlaDpas) (m n : Nat) : Word :=
  dpasSlab 16 (bf16ReadA rf d.srcA) (bf16ReadB rf d.srcB) m n

/-- A source read above a written C block is unchanged. -/
theorem bf16ReadA_writeTileC (rf : RegFile) (C : Nat → Nat → Word)
    (readBase writeBase : Nat) (h : writeBase + 8 ≤ readBase) :
    bf16ReadA (writeTileC rf writeBase C) readBase = bf16ReadA rf readBase := by
  funext m k
  unfold bf16ReadA
  rw [readTileA_writeTileC_above _ _ readBase writeBase m k (by omega)]

/-- The same for B. -/
theorem bf16ReadB_writeTileC (rf : RegFile) (C : Nat → Nat → Word)
    (readBase writeBase : Nat) (h : writeBase + 8 ≤ readBase) :
    bf16ReadB (writeTileC rf writeBase C) readBase = bf16ReadB rf readBase := by
  funext k n
  unfold bf16ReadB
  rw [readTileB_writeTileC_above _ _ readBase 0 writeBase k n (by omega)]

/-- The BF16 DPAS step: write both accumulator blocks with the decoded slab. -/
def tlaBf16Step (rf : RegFile) (d : TlaDpas) : RegFile :=
  let C0 := readTileC rf d.acc0
  let C1 := readTileC rf d.acc1
  writeTileC (writeTileC rf d.acc0 (fun m n => C0 m n + tlaBf16Slab rf d m n))
    d.acc1 (fun m n => C1 m n + tlaBf16Slab rf d m n)

/-- The BF16 chain. -/
def tlaBf16Run : List TlaDpas → RegFile → RegFile
  | [], rf => rf
  | d :: ds, rf => tlaBf16Run ds (tlaBf16Step rf d)

theorem tlaBf16Step_acc0 (rf : RegFile) (d : TlaDpas)
    (h0 : d.acc0 = 21) (h1 : d.acc1 = 13) (m n : Nat) (hm : m < 8) (hn : n < 8) :
    readTileC (tlaBf16Step rf d) 21 m n =
      readTileC rf 21 m n + tlaBf16Slab rf d m n := by
  simp only [tlaBf16Step, h0, h1]
  rw [readTileC_writeTileC_of_disjoint _ _ _ _ tileCDisjoint_21_13 m n hm hn]
  exact readTileC_writeTileC _ _ _ m n hm hn

theorem tlaBf16Step_acc1 (rf : RegFile) (d : TlaDpas)
    (h0 : d.acc0 = 21) (h1 : d.acc1 = 13) (m n : Nat) (hm : m < 8) (hn : n < 8) :
    readTileC (tlaBf16Step rf d) 13 m n =
      readTileC rf 13 m n + tlaBf16Slab rf d m n := by
  simp only [tlaBf16Step, h0, h1]
  exact readTileC_writeTileC _ _ _ m n hm hn

/-- A BF16 slab read above the accumulator blocks is unchanged by a step. -/
theorem tlaBf16Slab_step (rf : RegFile) (d e : TlaDpas)
    (h0 : d.acc0 = 21) (h1 : d.acc1 = 13)
    (hA : 29 ≤ e.srcA) (hB : 29 ≤ e.srcB) (m n : Nat) :
    tlaBf16Slab (tlaBf16Step rf d) e m n = tlaBf16Slab rf e m n := by
  unfold tlaBf16Slab
  simp only [tlaBf16Step, h0, h1]
  rw [bf16ReadA_writeTileC _ _ e.srcA 13 (by omega)]
  rw [bf16ReadA_writeTileC _ _ e.srcA 21 (by omega)]
  rw [bf16ReadB_writeTileC _ _ e.srcB 13 (by omega)]
  rw [bf16ReadB_writeTileC _ _ e.srcB 21 (by omega)]

set_option maxHeartbeats 2000000 in
/-- The first BF16 accumulator as the ordered slab sum. -/
theorem tlaBf16Run_acc0_sum (steps : List TlaDpas) (rf : RegFile)
    (hacc : ∀ d, d ∈ steps → d.acc0 = 21 ∧ d.acc1 = 13)
    (hA : ∀ d, d ∈ steps → 29 ≤ d.srcA)
    (hB : ∀ d, d ∈ steps → 29 ≤ d.srcB) :
    ∀ m n, m < 8 → n < 8 →
      readTileC (tlaBf16Run steps rf) 21 m n =
        readTileC rf 21 m n + (steps.map (fun d => tlaBf16Slab rf d m n)).sum := by
  induction steps generalizing rf with
  | nil => intro m n _ _; simp [tlaBf16Run]
  | cons d ds ih =>
      intro m n hm hn
      have hd : d.acc0 = 21 ∧ d.acc1 = 13 := hacc d (by simp)
      have hstep := tlaBf16Step_acc0 rf d hd.1 hd.2 m n hm hn
      have hmap : ds.map (fun e => tlaBf16Slab (tlaBf16Step rf d) e m n) =
          ds.map (fun e => tlaBf16Slab rf e m n) := by
        apply List.map_congr_left
        intro e he
        exact tlaBf16Slab_step rf d e hd.1 hd.2
          (hA e (by simp [he])) (hB e (by simp [he])) m n
      simp only [tlaBf16Run]
      rw [ih (tlaBf16Step rf d)
        (fun e he => hacc e (by simp [he]))
        (fun e he => hA e (by simp [he]))
        (fun e he => hB e (by simp [he])) m n hm hn]
      rw [hstep, hmap]
      simp [List.sum_cons, BitVec.add_assoc]

/-- The second BF16 accumulator as the ordered slab sum. -/
theorem tlaBf16Run_acc1_sum (steps : List TlaDpas) (rf : RegFile)
    (hacc : ∀ d, d ∈ steps → d.acc0 = 21 ∧ d.acc1 = 13)
    (hA : ∀ d, d ∈ steps → 29 ≤ d.srcA)
    (hB : ∀ d, d ∈ steps → 29 ≤ d.srcB) :
    ∀ m n, m < 8 → n < 8 →
      readTileC (tlaBf16Run steps rf) 13 m n =
        readTileC rf 13 m n + (steps.map (fun d => tlaBf16Slab rf d m n)).sum := by
  induction steps generalizing rf with
  | nil => intro m n _ _; simp [tlaBf16Run]
  | cons d ds ih =>
      intro m n hm hn
      have hd : d.acc0 = 21 ∧ d.acc1 = 13 := hacc d (by simp)
      have hstep := tlaBf16Step_acc1 rf d hd.1 hd.2 m n hm hn
      have hmap : ds.map (fun e => tlaBf16Slab (tlaBf16Step rf d) e m n) =
          ds.map (fun e => tlaBf16Slab rf e m n) := by
        apply List.map_congr_left
        intro e he
        exact tlaBf16Slab_step rf d e hd.1 hd.2
          (hA e (by simp [he])) (hB e (by simp [he])) m n
      simp only [tlaBf16Run]
      rw [ih (tlaBf16Step rf d)
        (fun e he => hacc e (by simp [he]))
        (fun e he => hA e (by simp [he]))
        (fun e he => hB e (by simp [he])) m n hm hn]
      rw [hstep, hmap]
      simp [List.sum_cons, BitVec.add_assoc]

/-- The real 32-step BF16 chain for both accumulators. -/
theorem realTlaGemmDpas_bf16_sum (rf : RegFile) (m n : Nat) (hm : m < 8) (hn : n < 8) :
    (readTileC (tlaBf16Run realTlaGemmDpas rf) 21 m n =
      readTileC rf 21 m n +
        (realTlaGemmDpas.map (fun d => tlaBf16Slab rf d m n)).sum) ∧
    (readTileC (tlaBf16Run realTlaGemmDpas rf) 13 m n =
      readTileC rf 13 m n +
        (realTlaGemmDpas.map (fun d => tlaBf16Slab rf d m n)).sum) := by
  have hacc : ∀ d, d ∈ realTlaGemmDpas → d.acc0 = 21 ∧ d.acc1 = 13 := by
    intro d hd
    have h := (List.all_eq_true.mp realTlaGemmDpas_accs) d hd
    simpa [Bool.and_eq_true] using h
  have hA : ∀ d, d ∈ realTlaGemmDpas → 29 ≤ d.srcA := by
    intro d hd
    exact of_decide_eq_true ((List.all_eq_true.mp realTlaGemmDpas_srcA_ge) d hd)
  have hB : ∀ d, d ∈ realTlaGemmDpas → 29 ≤ d.srcB := by
    intro d hd
    exact of_decide_eq_true ((List.all_eq_true.mp realTlaGemmDpas_srcB_ge) d hd)
  exact ⟨tlaBf16Run_acc0_sum realTlaGemmDpas rf hacc hA hB m n hm hn,
    tlaBf16Run_acc1_sum realTlaGemmDpas rf hacc hA hB m n hm hn⟩

end IntelGpu
