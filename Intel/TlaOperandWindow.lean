-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaWindow

@[expose] public section

/-!
# A/B operand windows and the flat register view

The DPAS model reads the B tile as `rf (base + n) k` with depth `k < 16`, i.e.
16 dwords per logical column, while a physical `rN:M` window provides eight
dwords per register. The view `flat rf r e = rf (r + e/8) (e%8)` identifies
the model's logical column register with a pair of physical registers.

Under this view the plain mainloop loads fill the DPAS operands exactly:
a load into `r(base):16` writes lane `n*8 + (k/8)*8 + k%8`, which is exactly
`readTileB (flat ·) base 0 k n`, and a load into `r(base):31` writes lane
`k*8 + m`, which is exactly `readTileA · base m k` (the A read is unaffected
by `flat` because its element index is below 8).
-/

namespace IntelGpu

/-- The flat register view: an element index `e` above 7 continues in the
next register. -/
def flat (rf : RegFile) : RegFile :=
  fun r e => rf (r + e / 8) (e % 8)

theorem readTileB_flat (rf : RegFile) (base k n : Nat) :
    readTileB (flat rf) base 0 k n = rf (base + n + k / 8) (k % 8) := by
  unfold readTileB flat
  simp 

theorem readTileA_flat (rf : RegFile) (base m k : Nat) (hm : m < 8) :
    readTileA (flat rf) base m k = readTileA rf base m k := by
  unfold readTileA flat
  rw [Nat.div_eq_of_lt hm, Nat.mod_eq_of_lt hm, Nat.add_zero]

/-- The B lane written by a load into `r(base):16` for depth `k`, column `n`. -/
def bLane (n k : Nat) : Nat := n * 8 + (k / 8) * 8 + k % 8

theorem bLane_lt (n k : Nat) (hn : n < 8) (hk : k < 16) : bLane n k < 128 := by
  unfold bLane
  omega

/-- A load into a 16-register window fills the B tile under the flat view. -/
theorem readTileB_window (rf : RegFile) (e : Exec) (f : Nat → Word)
    (base k n : Nat) (hn : n < 8) (hk : k < 16)
    (ha : e.elementActive (bLane n k) = true) :
    readTileB (flat (writeWindow rf ⟨base, 16⟩ e f)) base 0 k n =
      f (bLane n k) := by
  unfold readTileB flat bLane
  simp only [Nat.zero_add]
  change writeWindow rf ⟨base, 16⟩ e f (base + n + k / 8) (k % 8) = f (n * 8 + (k / 8) * 8 + k % 8)
  have hbc : base ≤ base + n + k / 8 := by omega
  have hlt : base + n + k / 8 < base + 16 := by omega
  have hk8 : k % 8 < 8 := Nat.mod_lt _ (by decide)
  have hsub : base + n + k / 8 - base = n + k / 8 := by omega
  have hidx : (⟨base, 16⟩ : TlaWindow).index (base + n + k / 8) (k % 8) =
      some (n * 8 + (k / 8) * 8 + k % 8) := by
    unfold TlaWindow.index
    rw [ite_eq_left ⟨hbc, hlt, hk8⟩]
    congr 1
    rw [hsub]
    omega
  exact writeWindow_active rf ⟨base, 16⟩ e f _ _ _ hidx ha

/-- The A lane written by a load into `r(base):31` for depth `k`, row `m`. -/
def aLane (m k : Nat) : Nat := k * 8 + m

theorem aLane_lt (m k : Nat) (hm : m < 8) (hk : k < 16) : aLane m k < 248 := by
  unfold aLane
  omega

/-- A load into a 31-register window fills the A tile. -/
theorem readTileA_window (rf : RegFile) (e : Exec) (f : Nat → Word)
    (base m k : Nat) (hm : m < 8) (hk : k < 16)
    (ha : e.elementActive (aLane m k) = true) :
    readTileA (writeWindow rf ⟨base, 31⟩ e f) base m k = f (aLane m k) := by
  unfold readTileA aLane
  change writeWindow rf ⟨base, 31⟩ e f (base + k) m = f (k * 8 + m)
  have hbc : base ≤ base + k := by omega
  have hlt : base + k < base + 31 := by omega
  have hsub : base + k - base = k := by omega
  have hidx : (⟨base, 31⟩ : TlaWindow).index (base + k) m = some (k * 8 + m) := by
    unfold TlaWindow.index
    rw [ite_eq_left ⟨hbc, hlt, hm⟩]
    congr 1
    rw [hsub]
  exact writeWindow_active rf ⟨base, 31⟩ e f _ _ _ hidx ha

end IntelGpu
