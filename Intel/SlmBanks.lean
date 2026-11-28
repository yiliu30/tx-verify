-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.Slm

@[expose] public section

/-!
# SLM banks, bank conflicts, and XOR swizzling

`Intel.Slm` models the SLM contents and barrier ordering but deliberately omits
bank conflicts. This module adds a small conflict model and proves the two
standard layout facts: consecutive words and a broadcast are cheap, while a
stride-2 access or a naive column access serializes, and an XOR swizzle repairs
the column access without hurting a row access.

The bank model is:

- SLM is word-addressed with 32 banks. Word address `a` is in bank `a % 32`.
- A lane group presents one access list, one word address per active lane, and
  issues one request for the group.
- A bank can service one distinct word per transaction. If `k` lanes in the
  request hit the same bank at distinct words, that bank serializes the request
  into `k` transactions; the request costs the maximum such `k`.
- A broadcast is the stated exception: if every lane presents the same address,
  the hardware serves the whole group in one transaction. This is reflected in
  `transactionCount`, while `maxConflict` still reports the strict bank count.
- There is no dual-porting, bank-width effect, byte-lane effect, replay,
  backpressure, arbitration latency, or cross-request concurrency. The model is
  a serialization count, not a hardware timing or conformance claim.

The strict conflict predicate `ConflictFree` requires the banks of all
presented addresses to be distinct. A broadcast is therefore not
`ConflictFree`, but it is one transaction under `transactionCount`.

Main results:

- `consecutive_conflictFree`: any 32 consecutive words use all 32 banks once.
- `maxConflict_stride2_zero` and `stride2_zero_transactionCount`: the 32-word
  stride-2 access has 16 banks used twice, so its cost is two transactions.
- `swizzleRow_conflictFree` and `swizzleColumn_conflictFree`: the XOR layout
  `row * 32 + (col ^ row)` is conflict-free for a full row and for a full
  column.
- `transactionCount_conflictFree`: a nonempty conflict-free request costs one
  transaction.
- `maxConflict_naiveColumn`, `naiveColumn_transactionCount`,
  `maxConflict_swizzleColumn`: the naive column repeats one bank 32 times and
  costs 32 transactions, while the swizzled column costs one.
- `banksOf_naiveColumn_zero` and `banksOf_swizzleColumn_zero`: the exact bank
  sets for the negative test are `[0, ..., 0]` versus `[0, ..., 31]`.
- `broadcast_transactionCount` and `maxConflict_broadcast`: a 32-lane broadcast
  has strict occupancy 32 but the modeled cost is one transaction.
-/

namespace IntelGpu

/-- The SLM bank width: 32 word-addressed banks. -/
def bankTotal : Nat := 32

theorem bankTotal_pos : 0 < bankTotal := by decide

theorem bankTotal_ne_zero : bankTotal ≠ 0 := by decide

/-- The bank of a word address: word address modulo 32. -/
def bankOf (addr : Nat) : Nat := addr % bankTotal

/-- The banks touched by an access list, in lane order. -/
def banksOf (addrs : List Nat) : List Nat := addrs.map bankOf

/-- Addresses `base, base + stride, ..., base + (count - 1) * stride`. -/
def laneGroup (base stride count : Nat) : List Nat :=
  (List.range count).map (fun i => base + i * stride)

/-- One full warp of consecutive words. -/
def consecutive (base : Nat) : List Nat := laneGroup base 1 bankTotal

/-- One full warp with a two-word stride. -/
def stride2 (base : Nat) : List Nat := laneGroup base 2 bankTotal

/-- All lanes present one address, so the hardware can broadcast the word. -/
def Broadcast (addrs : List Nat) : Prop :=
  addrs ≠ [] ∧ ∀ a ∈ addrs, ∀ b ∈ addrs, a = b

instance broadcastDecidable (addrs : List Nat) : Decidable (Broadcast addrs) := by
  unfold Broadcast
  infer_instance

/-- Strict bank-conflict freedom: every presented address maps to a distinct
bank. -/
def ConflictFree (addrs : List Nat) : Prop := (banksOf addrs).Nodup

/-- How many lanes of `addrs` hit bank `b`. -/
def bankCount (addrs : List Nat) (b : Nat) : Nat := (banksOf addrs).count b

/-- The strict serialization width: the maximum number of lanes on one bank. -/
def maxConflict (addrs : List Nat) : Nat :=
  (List.range bankTotal).foldl (fun m b => max m (bankCount addrs b)) 0

/-- Transactions charged for one lane-group request. A broadcast is one
transaction; otherwise every bank serializes its distinct-word hits. -/
def transactionCount (addrs : List Nat) : Nat :=
  if Broadcast addrs then 1 else maxConflict addrs

/-! ## Conflict counting -/

theorem foldl_max_ge_acc (l : List Nat) (f : Nat → Nat) (a : Nat) :
    a ≤ l.foldl (fun m b => max m (f b)) a := by
  induction l generalizing a with
  | nil => simp
  | cons x xs ih =>
      rw [List.foldl_cons]
      exact Nat.le_trans (Nat.le_max_left a (f x)) (ih (max a (f x)))

theorem foldl_max_mem (l : List Nat) (f : Nat → Nat) (a : Nat) {b : Nat}
    (hb : b ∈ l) : f b ≤ l.foldl (fun m b => max m (f b)) a := by
  induction l generalizing a with
  | nil => simp at hb
  | cons x xs ih =>
      rw [List.foldl_cons]
      by_cases hxb : b = x
      · subst b
        exact Nat.le_trans (Nat.le_max_right a (f x))
          (foldl_max_ge_acc xs f (max a (f x)))
      · exact ih (max a (f x)) ((List.mem_cons.mp hb).resolve_left hxb)

theorem foldl_max_le (l : List Nat) (f : Nat → Nat) (a k : Nat) (ha : a ≤ k)
    (h : ∀ b ∈ l, f b ≤ k) : l.foldl (fun m b => max m (f b)) a ≤ k := by
  induction l generalizing a with
  | nil => simpa using ha
  | cons x xs ih =>
      rw [List.foldl_cons]
      exact ih (max a (f x)) (Nat.max_le.mpr ⟨ha, h x (by simp)⟩)
        (fun b hb => h b (by simp [hb]))

/-- A bank's occupancy is at most the request-wide maximum. -/
theorem le_maxConflict (addrs : List Nat) {b : Nat} (hb : b < bankTotal) :
    bankCount addrs b ≤ maxConflict addrs := by
  unfold maxConflict
  exact foldl_max_mem (List.range bankTotal) (bankCount addrs) 0 (by simpa using hb)

/-- A uniform occupancy bound bounds the request-wide maximum. -/
theorem maxConflict_le (addrs : List Nat) {k : Nat}
    (h : ∀ b < bankTotal, bankCount addrs b ≤ k) : maxConflict addrs ≤ k := by
  unfold maxConflict
  exact foldl_max_le (List.range bankTotal) (bankCount addrs) 0 k (by omega)
    (fun b hb => h b (by simpa using hb))

theorem bankCount_le_length (addrs : List Nat) (b : Nat) :
    bankCount addrs b ≤ addrs.length := by
  unfold bankCount banksOf
  exact Nat.le_trans List.count_le_length (by simp)

theorem bankCount_le_one_of_conflictFree {addrs : List Nat}
    (h : ConflictFree addrs) (b : Nat) : bankCount addrs b ≤ 1 :=
  List.nodup_iff_count.mp h b

/-- A nonempty conflict-free request has maximum occupancy one. -/
theorem maxConflict_eq_one_of_conflictFree {addrs : List Nat}
    (h : ConflictFree addrs) (hne : addrs ≠ []) : maxConflict addrs = 1 := by
  have hle : maxConflict addrs ≤ 1 :=
    maxConflict_le addrs (fun b _ => bankCount_le_one_of_conflictFree h b)
  have hge : 1 ≤ maxConflict addrs := by
    cases addrs with
    | nil => contradiction
    | cons a as =>
        have hb : bankOf a < bankTotal := Nat.mod_lt _ bankTotal_pos
        have hmem : bankOf a ∈ banksOf (a :: as) := by simp [banksOf]
        have hcount : 1 ≤ bankCount (a :: as) (bankOf a) := List.count_pos_iff.mpr hmem
        exact Nat.le_trans hcount (le_maxConflict (a :: as) hb)
  omega

/-- A nonempty conflict-free request costs one transaction. -/
theorem transactionCount_conflictFree {addrs : List Nat} (h : ConflictFree addrs)
    (hne : addrs ≠ []) : transactionCount addrs = 1 := by
  by_cases hb : Broadcast addrs
  · simp [transactionCount, hb]
  · simp [transactionCount, hb, maxConflict_eq_one_of_conflictFree h hne]

/-- Outside the broadcast rule, the request costs its strict k-way conflict. -/
theorem transactionCount_of_not_broadcast {addrs : List Nat} {k : Nat}
    (hb : ¬ Broadcast addrs) (hk : maxConflict addrs = k) :
    transactionCount addrs = k := by
  simp [transactionCount, hb, hk]

/-! ## Consecutive words and stride two -/

theorem range_pairwise_bounded (n : Nat) :
    List.Pairwise (fun i j => i < n ∧ j < n ∧ i ≠ j) (List.range n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.pairwise_append]
    refine ⟨?_, by simp, ?_⟩
    · refine List.Pairwise.imp ?_ ih
      intro i j h
      exact ⟨by omega, by omega, h.2.2⟩
    · intro a ha b hb
      have hb' : b = n := by simpa using hb
      subst b
      have ha' : a < n := by simpa using ha
      exact ⟨by omega, by omega, by omega⟩

theorem add_mod_injective {base i j : Nat} (hi : i < bankTotal) (hj : j < bankTotal)
    (h : (base + i) % bankTotal = (base + j) % bankTotal) : i = j := by
  simp [bankTotal] at hi hj h
  omega

theorem banksOf_consecutive (base : Nat) :
    banksOf (consecutive base) =
      (List.range bankTotal).map (fun i => (base + i) % bankTotal) := by
  rw [banksOf, consecutive, laneGroup, List.map_map]
  apply List.map_congr_left
  intro i _
  simp [bankOf]

/-- Thirty-two consecutive words use every bank exactly once, for any base. -/
theorem consecutive_conflictFree (base : Nat) : ConflictFree (consecutive base) := by
  unfold ConflictFree
  rw [banksOf_consecutive]
  refine List.Pairwise.map (fun i => (base + i) % bankTotal) ?_
    (range_pairwise_bounded bankTotal)
  intro i j h heq
  exact h.2.2 (add_mod_injective h.1 h.2.1 heq)

theorem consecutive_nonempty (base : Nat) : consecutive base ≠ [] := by
  simp [consecutive, laneGroup, bankTotal_ne_zero]

theorem consecutive_transactionCount (base : Nat) :
    transactionCount (consecutive base) = 1 :=
  transactionCount_conflictFree (consecutive_conflictFree base) (consecutive_nonempty base)

/-- Exact bank list for a zero-based stride-2 warp: every even bank, twice. -/
theorem banksOf_stride2_zero :
    banksOf (stride2 0) =
      (List.range 16).map (fun i => 2 * i) ++ (List.range 16).map (fun i => 2 * i) := by
  decide

/-- The strict conflict width of the stride-2 warp is two. -/
theorem maxConflict_stride2_zero : maxConflict (stride2 0) = 2 := by
  decide

theorem stride2_zero_not_conflictFree : ¬ ConflictFree (stride2 0) := by
  intro h
  have hne : stride2 0 ≠ [] := by
    simp [stride2, laneGroup, bankTotal_ne_zero]
  have h1 := maxConflict_eq_one_of_conflictFree h hne
  rw [maxConflict_stride2_zero] at h1
  omega

theorem stride2_zero_not_broadcast : ¬ Broadcast (stride2 0) := by
  intro h
  have h01 := h.2 0 (by decide) 2 (by decide)
  omega

/-- The stride-2 warp costs two transactions. -/
theorem stride2_zero_transactionCount : transactionCount (stride2 0) = 2 :=
  transactionCount_of_not_broadcast stride2_zero_not_broadcast maxConflict_stride2_zero

/-! ## Broadcast -/

def broadcast (addr : Nat) : List Nat := List.replicate bankTotal addr

theorem broadcast_is_broadcast (addr : Nat) : Broadcast (broadcast addr) := by
  refine ⟨by simp [broadcast, bankTotal_ne_zero], ?_⟩
  intro a ha b hb
  exact (List.eq_of_mem_replicate ha).trans (List.eq_of_mem_replicate hb).symm

/-- A broadcast is one transaction under the stated rule. -/
theorem broadcast_transactionCount (addr : Nat) : transactionCount (broadcast addr) = 1 := by
  simp [transactionCount, broadcast_is_broadcast addr]

/-- Strict bank occupancy still sees all 32 broadcast lanes. -/
theorem maxConflict_broadcast (addr : Nat) : maxConflict (broadcast addr) = bankTotal := by
  apply Nat.le_antisymm
  · apply maxConflict_le
    intro b _
    calc bankCount (broadcast addr) b ≤ (broadcast addr).length := bankCount_le_length _ _
      _ = bankTotal := by simp [broadcast]
  · have hb : bankOf addr < bankTotal := Nat.mod_lt _ bankTotal_pos
    have hcount : bankCount (broadcast addr) (bankOf addr) = bankTotal := by
      unfold bankCount banksOf broadcast
      rw [List.map_replicate, List.count_replicate_self]
    calc bankTotal = bankCount (broadcast addr) (bankOf addr) := hcount.symm
      _ ≤ maxConflict (broadcast addr) := le_maxConflict _ hb

/-! ## XOR swizzle -/

/-- The swizzled bank for `(row, col)`: `col XOR (row % 32)`, reduced to five
bits. -/
def swizzleBank (row col : Nat) : Nat :=
  (col ^^^ (row % bankTotal)) % bankTotal

/-- Naive row-major layout with a row stride of 32 words. -/
def naiveAddr (row col : Nat) : Nat := row * bankTotal + col

/-- XOR-swizzled row-major layout. The low five address bits hold
`col XOR row`. -/
def swizzleAddr (row col : Nat) : Nat := row * bankTotal + swizzleBank row col

/-- A full row: all 32 columns at one fixed row. -/
def rowAccess (layout : Nat → Nat → Nat) (row : Nat) : List Nat :=
  (List.range bankTotal).map (fun col => layout row col)

/-- A full column: all 32 rows at one fixed column. -/
def columnAccess (layout : Nat → Nat → Nat) (col : Nat) : List Nat :=
  (List.range bankTotal).map (fun row => layout row col)

theorem xor_lt_bankTotal {a b : Nat} (ha : a < bankTotal) (hb : b < bankTotal) :
    a ^^^ b < bankTotal := by
  simpa [bankTotal] using Nat.xor_lt_two_pow (n := 5)
    (by simpa [bankTotal] using ha) (by simpa [bankTotal] using hb)

theorem swizzleBank_eq_xor (row col : Nat) (hcol : col < bankTotal) :
    swizzleBank row col = col ^^^ (row % bankTotal) := by
  exact Nat.mod_eq_of_lt (xor_lt_bankTotal hcol (Nat.mod_lt _ bankTotal_pos))

theorem xor_cancel_right {a b c : Nat} (h : a ^^^ c = b ^^^ c) : a = b := by
  have := congrArg (fun x => x ^^^ c) h
  simpa [Nat.xor_assoc] using this

theorem xor_cancel_left {a b c : Nat} (h : c ^^^ a = c ^^^ b) : a = b := by
  have h' := congrArg (fun x => c ^^^ x) h
  calc
    a = c ^^^ (c ^^^ a) := by rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
    _ = c ^^^ (c ^^^ b) := h'
    _ = b := by rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

theorem swizzleBank_inj_col {row c1 c2 : Nat} (h1 : c1 < bankTotal)
    (h2 : c2 < bankTotal) (h : swizzleBank row c1 = swizzleBank row c2) :
    c1 = c2 := by
  rw [swizzleBank_eq_xor row c1 h1, swizzleBank_eq_xor row c2 h2] at h
  exact xor_cancel_right h

theorem swizzleBank_inj_row {row1 row2 col : Nat} (h1 : row1 < bankTotal)
    (h2 : row2 < bankTotal) (hc : col < bankTotal)
    (h : swizzleBank row1 col = swizzleBank row2 col) : row1 = row2 := by
  rw [swizzleBank_eq_xor row1 col hc, swizzleBank_eq_xor row2 col hc] at h
  have h' : col ^^^ row1 = col ^^^ row2 := by
    simpa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] using h
  exact xor_cancel_left h'

theorem bankOf_naiveAddr (row col : Nat) :
    bankOf (naiveAddr row col) = col % bankTotal := by
  simp [bankOf, naiveAddr]

theorem bankOf_swizzleAddr (row col : Nat) :
    bankOf (swizzleAddr row col) = swizzleBank row col := by
  simp [bankOf, swizzleAddr, swizzleBank]

theorem banksOf_naiveColumn (col : Nat) :
    banksOf (columnAccess naiveAddr col) =
      List.replicate bankTotal (col % bankTotal) := by
  rw [banksOf, columnAccess, List.map_map]
  rw [show (bankOf ∘ fun row => naiveAddr row col) =
      (fun _ => col % bankTotal) from by
    funext row
    exact bankOf_naiveAddr row col]
  simp [List.map_const']

theorem banksOf_swizzleColumn (col : Nat) :
    banksOf (columnAccess swizzleAddr col) =
      (List.range bankTotal).map (fun row => swizzleBank row col) := by
  simp [banksOf, columnAccess, bankOf_swizzleAddr]

theorem banksOf_swizzleRow (row : Nat) :
    banksOf (rowAccess swizzleAddr row) =
      (List.range bankTotal).map (fun col => swizzleBank row col) := by
  simp [banksOf, rowAccess, bankOf_swizzleAddr]

/-- The swizzle preserves a full consecutive-row access: all 32 columns of any
row still use 32 distinct banks. -/
theorem swizzleRow_conflictFree (row : Nat) : ConflictFree (rowAccess swizzleAddr row) := by
  unfold ConflictFree
  rw [banksOf_swizzleRow]
  refine List.Pairwise.map (fun col => swizzleBank row col) ?_
    (range_pairwise_bounded bankTotal)
  intro c1 c2 h heq
  exact h.2.2 (swizzleBank_inj_col h.1 h.2.1 heq)

/-- The swizzle removes the naive transpose conflict: all 32 rows of any column
use 32 distinct banks. -/
theorem swizzleColumn_conflictFree (col : Nat) (hc : col < bankTotal) :
    ConflictFree (columnAccess swizzleAddr col) := by
  unfold ConflictFree
  rw [banksOf_swizzleColumn]
  refine List.Pairwise.map (fun row => swizzleBank row col) ?_
    (range_pairwise_bounded bankTotal)
  intro r1 r2 h heq
  exact h.2.2 (swizzleBank_inj_row h.1 h.2.1 hc heq)

theorem rowAccess_nonempty (layout : Nat → Nat → Nat) (row : Nat) :
    rowAccess layout row ≠ [] := by
  simp [rowAccess, bankTotal_ne_zero]

theorem columnAccess_nonempty (layout : Nat → Nat → Nat) (col : Nat) :
    columnAccess layout col ≠ [] := by
  simp [columnAccess, bankTotal_ne_zero]

/-- A swizzled row costs one transaction. -/
theorem swizzleRow_transactionCount (row : Nat) :
    transactionCount (rowAccess swizzleAddr row) = 1 :=
  transactionCount_conflictFree (swizzleRow_conflictFree row)
    (rowAccess_nonempty swizzleAddr row)

/-- A swizzled column costs one transaction. -/
theorem swizzleColumn_transactionCount (col : Nat) (hc : col < bankTotal) :
    transactionCount (columnAccess swizzleAddr col) = 1 :=
  transactionCount_conflictFree (swizzleColumn_conflictFree col hc)
    (columnAccess_nonempty swizzleAddr col)

/-- A full swizzled row has strict maximum occupancy one. -/
theorem maxConflict_swizzleRow (row : Nat) :
    maxConflict (rowAccess swizzleAddr row) = 1 :=
  maxConflict_eq_one_of_conflictFree (swizzleRow_conflictFree row)
    (rowAccess_nonempty swizzleAddr row)

/-- A full swizzled column has strict maximum occupancy one. -/
theorem maxConflict_swizzleColumn (col : Nat) (hc : col < bankTotal) :
    maxConflict (columnAccess swizzleAddr col) = 1 :=
  maxConflict_eq_one_of_conflictFree (swizzleColumn_conflictFree col hc)
    (columnAccess_nonempty swizzleAddr col)

/-! ## Negative test: naive transpose versus swizzle -/

/-- The naive column repeats one bank in every lane. -/
theorem banksOf_naiveColumn_zero :
    banksOf (columnAccess naiveAddr 0) = List.replicate bankTotal 0 := by
  simp [banksOf_naiveColumn]

/-- The zero-column naive access has 32-way conflict. -/
theorem maxConflict_naiveColumn (col : Nat) :
    maxConflict (columnAccess naiveAddr col) = bankTotal := by
  apply Nat.le_antisymm
  · apply maxConflict_le
    intro b _
    calc bankCount (columnAccess naiveAddr col) b
        ≤ (columnAccess naiveAddr col).length := bankCount_le_length _ _
      _ = bankTotal := by simp [columnAccess]
  · have hb : col % bankTotal < bankTotal := Nat.mod_lt _ bankTotal_pos
    have hcount : bankCount (columnAccess naiveAddr col) (col % bankTotal) = bankTotal := by
      unfold bankCount
      rw [banksOf_naiveColumn, List.count_replicate_self]
    calc bankTotal = bankCount (columnAccess naiveAddr col) (col % bankTotal) := hcount.symm
      _ ≤ maxConflict (columnAccess naiveAddr col) := le_maxConflict _ hb

theorem naiveColumn_not_broadcast (col : Nat) : ¬ Broadcast (columnAccess naiveAddr col) := by
  intro h
  have h0 : naiveAddr 0 col ∈ columnAccess naiveAddr col :=
    List.mem_map.mpr ⟨0, by simpa using bankTotal_pos, rfl⟩
  have h1 : naiveAddr 1 col ∈ columnAccess naiveAddr col :=
    List.mem_map.mpr ⟨1, by decide, rfl⟩
  have h01 := h.2 (naiveAddr 0 col) h0 (naiveAddr 1 col) h1
  unfold naiveAddr at h01
  have hpos := bankTotal_pos
  omega

/-- The naive transpose column costs all 32 transactions. -/
theorem naiveColumn_transactionCount (col : Nat) :
    transactionCount (columnAccess naiveAddr col) = bankTotal :=
  transactionCount_of_not_broadcast (naiveColumn_not_broadcast col)
    (maxConflict_naiveColumn col)

/-- The zero-column swizzle uses every bank exactly once. -/
theorem banksOf_swizzleColumn_zero :
    banksOf (columnAccess swizzleAddr 0) = List.range bankTotal := by
  decide

end IntelGpu
