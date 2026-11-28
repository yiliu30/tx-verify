-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaFmhaPv

@[expose] public section

/-!
# PV phase census

The 32 PV atoms split into 16 accumulator groups of two atoms each. Every
group satisfies the fixed-accumulator chain conditions, so `pvGroup_sum_of_mem`
gives the two-pass slab sum for any group named by the census.

As in `Intel/TlaFmhaPv`, the sums are for DPAS-only sub-runs; the real
schedule reloads A/B between the groups.
-/

namespace IntelGpu

/-- The atoms of one PV accumulator group. -/
def pvGroup (a : Nat) : List FmhaDpas := pvDpas.filter (fun d => d.acc0 = a)

/-- The 16 PV accumulator bases. -/
def pvAccs : List Nat :=
  [74, 82, 90, 98, 106, 114, 122, 130, 138, 146, 154, 162, 170, 178, 186, 194]

theorem pvGroup_sum (a : Nat) (rf : RegFile) (m n : Nat) (hm : m < 8) (hn : n < 8)
    (hsrc : (pvGroup a).all (fun d =>
      (a + 8 ≤ d.srcA || d.srcA + 8 ≤ a) &&
      (a + 8 ≤ d.srcB || d.srcB + 8 ≤ a)) = true) :
    readTileC (fmhaAtomRun (pvGroup a) rf) a m n =
      readTileC rf a m n +
        ((pvGroup a).map (fun d => fmhaBf16Slab rf d m n)).sum := by
  refine fmhaAtomRun_fixed_acc (pvGroup a) rf a ?_ ?_ ?_ m n hm hn
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
/-- Every group has two atoms and satisfies the chain source conditions. -/
theorem pvAccs_ok :
    pvAccs.all (fun a =>
      (pvGroup a).length = 2 &&
      (pvGroup a).all (fun d =>
        (a + 8 ≤ d.srcA || d.srcA + 8 ≤ a) &&
        (a + 8 ≤ d.srcB || d.srcB + 8 ≤ a))) = true := by
  decide

set_option maxRecDepth 1000000 in
/-- Every PV atom belongs to a census group. -/
theorem pvDpas_accs_mem :
    pvDpas.all (fun d => decide (d.acc0 ∈ pvAccs)) = true := by
  decide

/-- A census group has two atoms. -/
theorem pvGroup_length_of_mem {a : Nat} (ha : a ∈ pvAccs) :
    (pvGroup a).length = 2 := by
  have h := (List.all_eq_true.mp pvAccs_ok) a ha
  simp only [Bool.and_eq_true] at h
  exact of_decide_eq_true h.1

/-- The two-pass slab sum for any census group. -/
theorem pvGroup_sum_of_mem {a : Nat} (ha : a ∈ pvAccs) (rf : RegFile) (m n : Nat)
    (hm : m < 8) (hn : n < 8) :
    readTileC (fmhaAtomRun (pvGroup a) rf) a m n =
      readTileC rf a m n +
        ((pvGroup a).map (fun d => fmhaBf16Slab rf d m n)).sum := by
  have h := (List.all_eq_true.mp pvAccs_ok) a ha
  simp only [Bool.and_eq_true] at h
  exact pvGroup_sum a rf m n hm hn h.2

end IntelGpu
