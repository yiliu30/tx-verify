-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaFmhaPv

@[expose] public section

/-!
# The QK^T DPAS chain

The 32 QK^T atoms accumulate into four blocks (`r42`, `r50`, `r58`, `r66`),
eight atoms each. Every A/B source of a group is either entirely above or
entirely below the group accumulator, so the fixed-accumulator chain theorem
applies: each block ends as its initial value plus the ordered slab sum of
its eight atoms.
-/

namespace IntelGpu

/-- The atoms of one QK^T accumulator group. -/
def qkGroup (a : Nat) : List FmhaDpas := qkDpas.filter (fun d => d.acc0 = a)

theorem qkGroup_sum (a : Nat) (rf : RegFile) (m n : Nat) (hm : m < 8) (hn : n < 8)
    (hsrc : (qkGroup a).all (fun d =>
      (a + 8 ≤ d.srcA || d.srcA + 8 ≤ a) &&
      (a + 8 ≤ d.srcB || d.srcB + 8 ≤ a)) = true) :
    readTileC (fmhaAtomRun (qkGroup a) rf) a m n =
      readTileC rf a m n +
        ((qkGroup a).map (fun d =>
          dpasSlab 16 (readTileA rf d.srcA) (readTileB rf d.srcB 0) m n)).sum := by
  refine fmhaAtomRun_fixed_acc (qkGroup a) rf a ?_ ?_ ?_ m n hm hn
  · intro d hd
    have h := (List.mem_filter.mp hd).2
    simpa using h
  · intro d hd
    have h := (List.all_eq_true.mp hsrc) d hd
    simp only [Bool.and_eq_true] at h
    simpa [Bool.or_eq_true] using h.1
  · intro d hd
    have h := (List.all_eq_true.mp hsrc) d hd
    simp only [Bool.and_eq_true] at h
    simpa [Bool.or_eq_true] using h.2

set_option maxRecDepth 1000000 in
theorem qk42_length : (qkGroup 42).length = 8 := by decide

set_option maxRecDepth 1000000 in
theorem qk50_length : (qkGroup 50).length = 8 := by decide

set_option maxRecDepth 1000000 in
theorem qk58_length : (qkGroup 58).length = 8 := by decide

set_option maxRecDepth 1000000 in
theorem qk66_length : (qkGroup 66).length = 8 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
/-- The `r42` block is its initial value plus eight slabs. -/
theorem qk42_sum (rf : RegFile) (m n : Nat) (hm : m < 8) (hn : n < 8) :
    readTileC (fmhaAtomRun (qkGroup 42) rf) 42 m n =
      readTileC rf 42 m n +
        ((qkGroup 42).map (fun d =>
          dpasSlab 16 (readTileA rf d.srcA) (readTileB rf d.srcB 0) m n)).sum :=
  qkGroup_sum 42 rf m n hm hn (by decide)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
/-- The `r50` block is its initial value plus eight slabs. -/
theorem qk50_sum (rf : RegFile) (m n : Nat) (hm : m < 8) (hn : n < 8) :
    readTileC (fmhaAtomRun (qkGroup 50) rf) 50 m n =
      readTileC rf 50 m n +
        ((qkGroup 50).map (fun d =>
          dpasSlab 16 (readTileA rf d.srcA) (readTileB rf d.srcB 0) m n)).sum :=
  qkGroup_sum 50 rf m n hm hn (by decide)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
/-- The `r58` block is its initial value plus eight slabs. -/
theorem qk58_sum (rf : RegFile) (m n : Nat) (hm : m < 8) (hn : n < 8) :
    readTileC (fmhaAtomRun (qkGroup 58) rf) 58 m n =
      readTileC rf 58 m n +
        ((qkGroup 58).map (fun d =>
          dpasSlab 16 (readTileA rf d.srcA) (readTileB rf d.srcB 0) m n)).sum :=
  qkGroup_sum 58 rf m n hm hn (by decide)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
/-- The `r66` block is its initial value plus eight slabs. -/
theorem qk66_sum (rf : RegFile) (m n : Nat) (hm : m < 8) (hn : n < 8) :
    readTileC (fmhaAtomRun (qkGroup 66) rf) 66 m n =
      readTileC rf 66 m n +
        ((qkGroup 66).map (fun d =>
          dpasSlab 16 (readTileA rf d.srcA) (readTileB rf d.srcB 0) m n)).sum :=
  qkGroup_sum 66 rf m n hm hn (by decide)

end IntelGpu
