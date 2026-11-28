-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.FmhaExec

@[expose] public section

/-!
# T-step FMHA mainloop over depth-32 slabs

`Intel.FmhaExec` executes one decoded 8x8x32 DPAS at the operand bases
`⟨383, 335, 0, 39⟩`. A K tile of depth `32 * T` is `T` such instructions,
each reading the next depth slab. This module lifts the single register-level
step to that mainloop:

- `fmhaSlabA`/`fmhaSlabB` read operand slab `t` at depth `t * 32`;
- `fmhaMainloopSlabAt` runs one DPAS over slab `t`, accumulating into the
  same C block;
- `fmhaMainloopStepAt regs rf T` runs slabs `0 .. T-1`, with
  `fmhaMainloopStepAt_zero` and `fmhaMainloopStepAt_succ` as the recurrence
  `T + 1 = step T` and `T = 0` as the identity;
- `fmhaMainloopStepAt_c` identifies the C block after `T` steps with the
  incoming block plus `dpasRun` over the `T` depth-32 slabs, and
  `fmhaMainloopStepAt_c_dotMat` with `dotMat` at depth `T * 32`;
- `fmhaMainloopStepAt_frame` says every element outside the C block is
  unchanged;
- `fmhaMainloopStepAt_two_eq_atoms`/`fmhaMainloopStepAt_two_c_atoms`
  specialize `T = 2` (K = 64) to two K=32 atoms, and
  `fmhaMainloopStepAt_two_eq_halves`, via `fmhaAtom_eq_sum_halves`, splits
  those atoms into four K=16 halves;
- `fmhaMainloopPairAt_commute_and_sum` composes two mainloops on disjoint C
  blocks: they commute and each block receives its own `dpasRun` sum.

## Modelled register packing

As in `Intel.FmhaExec`, the operand layout is the logical tile packing:

- A element `(m, k)` is `rf (A + k) m`, so slab `t` reads registers
  `A + 32 * t .. A + 32 * t + 31`;
- B element `(k, n)` is `rf (B + n) (sub + k)`, so slab `t` reads element
  `sub + 32 * t + k` of registers `B .. B + 7`;
- C element `(m, n)` is `rf (C + m) n`.

The mainloop keeps one register-file snapshot for A and B while it
accumulates into the same C block, the logical analogue of reusing the
loaded operand registers across a DPAS chain. These maps are a model
assumption; they are not a decoded claim about the compiled kernel's physical
dword or byte lanes, and no hardware layout equivalence is asserted.
-/

namespace IntelGpu

/-! ## Depth slabs -/

/-- Operand A of depth slab `t`: depth `t * 32 + k` selects register
`base + t * 32 + k`, and row `m` selects the element. -/
def fmhaSlabA (rf : RegFile) (base t : Nat) : Nat → Nat → Word :=
  fun m k => readTileA rf base m (t * 32 + k)

/-- Operand B of depth slab `t`: depth `t * 32 + k` selects element
`sub + t * 32 + k` of register `base + n`. -/
def fmhaSlabB (rf : RegFile) (base sub t : Nat) : Nat → Nat → Word :=
  fun k n => readTileB rf base sub (t * 32 + k) n

/-- The depth-32 delta of slab `t`, without the accumulator. The A operand is
transposed into the depth-major form expected by `dpasSlab`. -/
def fmhaMainloopSlabDeltaAt (regs : DpasRegs) (rf : RegFile) (t : Nat) :
    Nat → Nat → Word :=
  fun m n => dpasSlab 32 (fun k m' => fmhaSlabA rf regs.src2 t m' k)
    (fmhaSlabB rf regs.src1 regs.src1Sub t) m n

/-- One DPAS over depth slab `t`, accumulated into the C block of `state`.
The A and B operands come from the fixed snapshot `rf`, so the only state
that changes is the C block. -/
def fmhaMainloopSlabAt (regs : DpasRegs) (rf : RegFile) (t : Nat)
    (state : RegFile) : RegFile :=
  fmhaDpasWith regs.dst (fmhaSlabA rf regs.src2 t)
    (fmhaSlabB rf regs.src1 regs.src1Sub t) state

/-- `T` value-level steps over slabs `0 .. T-1`; slab `T-1` is issued last.
`D t` is the depth-32 delta of slab `t`. -/
def fmhaMainloopTileAt (C : Nat → Nat → Word)
    (D : Nat → Nat → Nat → Word) (T : Nat) : Nat → Nat → Word :=
  match T with
  | 0 => C
  | T + 1 => fun m n => fmhaMainloopTileAt C D T m n + D T m n

/-! ## The register-file mainloop -/

/-- The `T`-step register-level mainloop at the operand bases `regs`: slabs
`0 .. T-1` accumulate into the same C block. -/
def fmhaMainloopStepAt (regs : DpasRegs) (rf : RegFile) (T : Nat) : RegFile :=
  match T with
  | 0 => rf
  | T + 1 => fmhaMainloopSlabAt regs rf T (fmhaMainloopStepAt regs rf T)

theorem fmhaMainloopStepAt_zero (regs : DpasRegs) (rf : RegFile) :
    fmhaMainloopStepAt regs rf 0 = rf := rfl

theorem fmhaMainloopStepAt_succ (regs : DpasRegs) (rf : RegFile) (T : Nat) :
    fmhaMainloopStepAt regs rf (T + 1) =
      fmhaMainloopSlabAt regs rf T (fmhaMainloopStepAt regs rf T) := rfl

theorem fmhaSlabA_zero (rf : RegFile) (base : Nat) :
    fmhaSlabA rf base 0 = readTileA rf base := by
  funext m k
  simp [fmhaSlabA]

theorem fmhaSlabB_zero (rf : RegFile) (base sub : Nat) :
    fmhaSlabB rf base sub 0 = readTileB rf base sub := by
  funext k n
  simp [fmhaSlabB]

/-- The first mainloop step is exactly the decoded single DPAS step. -/
theorem fmhaMainloopSlabAt_zero_eq_stepAt (regs : DpasRegs) (rf : RegFile) :
    fmhaMainloopSlabAt regs rf 0 rf = fmhaDpasStepAt regs rf := by
  simp [fmhaMainloopSlabAt, fmhaDpasStepAt, fmhaSlabA_zero, fmhaSlabB_zero]

theorem fmhaMainloopStepAt_one_eq_stepAt (regs : DpasRegs) (rf : RegFile) :
    fmhaMainloopStepAt regs rf 1 = fmhaDpasStepAt regs rf := by
  have h : fmhaMainloopStepAt regs rf 1 =
      fmhaMainloopSlabAt regs rf 0 (fmhaMainloopStepAt regs rf 0) := rfl
  rw [h, fmhaMainloopStepAt_zero]
  exact fmhaMainloopSlabAt_zero_eq_stepAt regs rf

/-! ## One slab into the C block -/

theorem writeTileC_writeTileC (rf : RegFile) (base : Nat)
    (C C' : Nat → Nat → Word) :
    writeTileC (writeTileC rf base C) base C' = writeTileC rf base C' := by
  funext r e
  unfold writeTileC
  by_cases h : inTileC base r e <;> simp [h]

theorem writeTileC_readTileC (rf : RegFile) (base : Nat) :
    writeTileC rf base (readTileC rf base) = rf := by
  funext r e
  unfold writeTileC readTileC
  by_cases h : inTileC base r e
  · simp [h, Nat.add_sub_cancel' h.1]
  · simp [h]

/-- Inside the C block, one slab step is the atom at its local origins. -/
theorem fmhaMainloopSlabAt_atom (regs : DpasRegs) (rf : RegFile) (t : Nat)
    (state : RegFile) (m n : Nat) (hm : m < 8) (hn : n < 8) :
    readTileC (fmhaMainloopSlabAt regs rf t state) regs.dst m n =
      fmhaAtom (fmhaSlabA rf regs.src2 t)
        (fmhaSlabB rf regs.src1 regs.src1Sub t)
        (readTileC state regs.dst) 0 0 m n := by
  simpa [fmhaMainloopSlabAt] using
    fmhaDpasWith_c regs.dst (fmhaSlabA rf regs.src2 t)
      (fmhaSlabB rf regs.src1 regs.src1Sub t) state m n hm hn

/-- Inside the C block, one slab step adds the slab's depth-32 delta. -/
theorem fmhaMainloopSlabAt_c (regs : DpasRegs) (rf : RegFile) (t : Nat)
    (state : RegFile) (m n : Nat) (hm : m < 8) (hn : n < 8) :
    readTileC (fmhaMainloopSlabAt regs rf t state) regs.dst m n =
      readTileC state regs.dst m n +
        fmhaMainloopSlabDeltaAt regs rf t m n := by
  rw [fmhaMainloopSlabAt_atom regs rf t state m n hm hn]
  simp [fmhaAtom, fmhaMainloopSlabDeltaAt]

/-- One slab step leaves every element outside the C block unchanged. -/
theorem fmhaMainloopSlabAt_frame (regs : DpasRegs) (rf : RegFile) (t : Nat)
    (state : RegFile) (r e : Nat) (h : ¬ inTileC regs.dst r e) :
    fmhaMainloopSlabAt regs rf t state r e = state r e := by
  simpa [fmhaMainloopSlabAt, fmhaDpasWith] using
    writeTileC_frame state regs.dst _ r e h

/-! ## Value of the T-step mainloop -/

/-- The tile-level mainloop is the incoming accumulator plus `dpasRun`. -/
theorem fmhaMainloopTileAt_dpasRun (regs : DpasRegs) (rf : RegFile)
    (T m n : Nat) :
    fmhaMainloopTileAt (readTileC rf regs.dst)
        (fmhaMainloopSlabDeltaAt regs rf) T m n =
      readTileC rf regs.dst m n +
        dpasRun (readTileA rf regs.src2)
          (readTileB rf regs.src1 regs.src1Sub) 0 0 32 T
          (fun _ _ => 0) m n := by
  induction T with
  | zero => simp [fmhaMainloopTileAt, dpasRun]
  | succ T ih =>
      simp only [fmhaMainloopTileAt]
      rw [ih]
      simp only [dpasRun, dpas, fmhaMainloopSlabDeltaAt, fmhaSlabA,
        Nat.zero_add]
      rw [BitVec.add_assoc]
      rfl

/-- The register mainloop is one write of the tile-level running sum. -/
theorem fmhaMainloopStepAt_eq_writeTileC (regs : DpasRegs) (rf : RegFile)
    (T : Nat) :
    fmhaMainloopStepAt regs rf T =
      writeTileC rf regs.dst
        (fmhaMainloopTileAt (readTileC rf regs.dst)
          (fmhaMainloopSlabDeltaAt regs rf) T) := by
  induction T with
  | zero =>
      rw [fmhaMainloopStepAt_zero]
      simpa [fmhaMainloopTileAt] using (writeTileC_readTileC rf regs.dst).symm
  | succ T ih =>
      rw [fmhaMainloopStepAt_succ, ih, fmhaMainloopSlabAt, fmhaDpasWith,
        writeTileC_writeTileC]
      apply writeTileC_congr_on_block
      intro m n hm hn
      have hread : readTileC
          (writeTileC rf regs.dst
            (fmhaMainloopTileAt (readTileC rf regs.dst)
              (fmhaMainloopSlabDeltaAt regs rf) T)) regs.dst m n =
          fmhaMainloopTileAt (readTileC rf regs.dst)
            (fmhaMainloopSlabDeltaAt regs rf) T m n :=
        readTileC_writeTileC rf regs.dst _ m n hm hn
      rw [show fmhaMainloopTileAt (readTileC rf regs.dst)
            (fmhaMainloopSlabDeltaAt regs rf) (T + 1) m n =
          fmhaMainloopTileAt (readTileC rf regs.dst)
            (fmhaMainloopSlabDeltaAt regs rf) T m n +
          fmhaMainloopSlabDeltaAt regs rf T m n from rfl]
      rw [← hread]
      simp [fmhaAtom, fmhaMainloopSlabDeltaAt]

/-- The C block after `T` steps is the tile-level running sum. -/
theorem fmhaMainloopStepAt_c_tile (regs : DpasRegs) (rf : RegFile)
    (T m n : Nat) (hm : m < 8) (hn : n < 8) :
    readTileC (fmhaMainloopStepAt regs rf T) regs.dst m n =
      fmhaMainloopTileAt (readTileC rf regs.dst)
        (fmhaMainloopSlabDeltaAt regs rf) T m n := by
  rw [fmhaMainloopStepAt_eq_writeTileC,
    readTileC_writeTileC _ regs.dst _ m n hm hn]

/-- After `T` steps the C block is the incoming block plus `dpasRun` over the
`T` depth-32 slabs. -/
theorem fmhaMainloopStepAt_c (regs : DpasRegs) (rf : RegFile)
    (T m n : Nat) (hm : m < 8) (hn : n < 8) :
    readTileC (fmhaMainloopStepAt regs rf T) regs.dst m n =
      readTileC rf regs.dst m n +
        dpasRun (readTileA rf regs.src2)
          (readTileB rf regs.src1 regs.src1Sub) 0 0 32 T
          (fun _ _ => 0) m n := by
  rw [fmhaMainloopStepAt_c_tile regs rf T m n hm hn]
  exact fmhaMainloopTileAt_dpasRun regs rf T m n

/-- Spec form: after `T` steps the C block is the incoming block plus the
depth-`T * 32` matrix dot product. -/
theorem fmhaMainloopStepAt_c_dotMat (regs : DpasRegs) (rf : RegFile)
    (T m n : Nat) (hm : m < 8) (hn : n < 8) :
    readTileC (fmhaMainloopStepAt regs rf T) regs.dst m n =
      readTileC rf regs.dst m n +
        dotMat (readTileA rf regs.src2)
          (readTileB rf regs.src1 regs.src1Sub) m n (T * 32) := by
  rw [fmhaMainloopStepAt_c regs rf T m n hm hn]
  rw [dpasRun_correct]
  simp

/-- Every element outside the C block is unchanged after `T` steps. -/
theorem fmhaMainloopStepAt_frame (regs : DpasRegs) (rf : RegFile)
    (T r e : Nat) (h : ¬ inTileC regs.dst r e) :
    fmhaMainloopStepAt regs rf T r e = rf r e := by
  induction T with
  | zero => rfl
  | succ T ih =>
      rw [fmhaMainloopStepAt_succ,
        fmhaMainloopSlabAt_frame regs rf T (fmhaMainloopStepAt regs rf T) r e h,
        ih]

/-! ## T = 2: two K=32 atoms -/

/-- The K=64 mainloop is two back-to-back depth-32 atoms, slab 0 then slab 1. -/
theorem fmhaMainloopStepAt_two_eq_atoms (regs : DpasRegs) (rf : RegFile) :
    fmhaMainloopStepAt regs rf 2 =
      fmhaMainloopSlabAt regs rf 1 (fmhaMainloopSlabAt regs rf 0 rf) := rfl

/-- Slab sums in the order the mainloop issues them. -/
theorem fmhaMainloopStepAt_two_c (regs : DpasRegs) (rf : RegFile)
    (m n : Nat) (hm : m < 8) (hn : n < 8) :
    readTileC (fmhaMainloopStepAt regs rf 2) regs.dst m n =
      readTileC rf regs.dst m n +
        fmhaMainloopSlabDeltaAt regs rf 0 m n +
        fmhaMainloopSlabDeltaAt regs rf 1 m n := by
  rw [fmhaMainloopStepAt_two_eq_atoms,
    fmhaMainloopSlabAt_c regs rf 1 (fmhaMainloopSlabAt regs rf 0 rf)
      m n hm hn,
    fmhaMainloopSlabAt_c regs rf 0 rf m n hm hn]

/-- Value form: the K=64 mainloop is the incoming block plus two K=32 atoms,
each written as its zero-accumulator `fmhaAtom` delta. -/
theorem fmhaMainloopStepAt_two_c_atoms (regs : DpasRegs) (rf : RegFile)
    (m n : Nat) (hm : m < 8) (hn : n < 8) :
    readTileC (fmhaMainloopStepAt regs rf 2) regs.dst m n =
      readTileC rf regs.dst m n +
        fmhaAtom (fmhaSlabA rf regs.src2 0)
          (fmhaSlabB rf regs.src1 regs.src1Sub 0) (fun _ _ => 0) 0 0 m n +
        fmhaAtom (fmhaSlabA rf regs.src2 1)
          (fmhaSlabB rf regs.src1 regs.src1Sub 1) (fun _ _ => 0) 0 0 m n := by
  rw [fmhaMainloopStepAt_two_c regs rf m n hm hn]
  simp [fmhaAtom, fmhaMainloopSlabDeltaAt]

/-- Value form with nested atoms: slab 1 accumulates onto slab 0's atom. -/
theorem fmhaMainloopStepAt_two_c_nested (regs : DpasRegs) (rf : RegFile)
    (m n : Nat) (hm : m < 8) (hn : n < 8) :
    readTileC (fmhaMainloopStepAt regs rf 2) regs.dst m n =
      fmhaAtom (fmhaSlabA rf regs.src2 1)
        (fmhaSlabB rf regs.src1 regs.src1Sub 1)
        (fun m' n' => fmhaAtom (fmhaSlabA rf regs.src2 0)
          (fmhaSlabB rf regs.src1 regs.src1Sub 0)
          (readTileC rf regs.dst) 0 0 m' n') 0 0 m n := by
  rw [fmhaMainloopStepAt_two_eq_atoms,
    fmhaMainloopSlabAt_atom regs rf 1 (fmhaMainloopSlabAt regs rf 0 rf)
      m n hm hn]
  apply fmhaAtom_congr
  · intro k _
    rfl
  · intro k _
    rfl
  · exact fmhaMainloopSlabAt_atom regs rf 0 rf m n hm hn

/-- K=64 value form: the mainloop adds the depth-64 matrix dot product. -/
theorem fmhaMainloopStepAt_two_c_dotMat (regs : DpasRegs) (rf : RegFile)
    (m n : Nat) (hm : m < 8) (hn : n < 8) :
    readTileC (fmhaMainloopStepAt regs rf 2) regs.dst m n =
      readTileC rf regs.dst m n +
        dotMat (readTileA rf regs.src2)
          (readTileB rf regs.src1 regs.src1Sub) m n 64 := by
  simpa using fmhaMainloopStepAt_c_dotMat regs rf 2 m n hm hn

/-- A shifted depth-16 half is the half at the corresponding global depth. -/
theorem fmhaHalfDelta_slab (A B : Nat → Nat → Word) (t u m n : Nat) :
    fmhaHalfDelta (fun m k => A m (t + k)) (fun k n => B (t + k) n)
        0 0 u m n =
      fmhaHalfDelta A B 0 0 (t + u) m n := by
  unfold fmhaHalfDelta
  simp only [Nat.zero_add]
  apply dpasSlab_congr_at 16 m n
  · intro k _
    congr 1
    omega
  · intro k _
    congr 1
    omega

/-- Each depth-32 slab is the sum of two depth-16 halves, by
`fmhaAtom_eq_sum_halves` at a zero accumulator. -/
theorem fmhaMainloopSlabDelta_eq_halves (regs : DpasRegs) (rf : RegFile)
    (t m n : Nat) :
    fmhaMainloopSlabDeltaAt regs rf t m n =
      fmhaHalfDelta (readTileA rf regs.src2)
          (readTileB rf regs.src1 regs.src1Sub) 0 0 (t * 32) m n +
        fmhaHalfDelta (readTileA rf regs.src2)
          (readTileB rf regs.src1 regs.src1Sub) 0 0 (t * 32 + 16) m n := by
  have h := fmhaAtom_eq_sum_halves (fmhaSlabA rf regs.src2 t)
    (fmhaSlabB rf regs.src1 regs.src1Sub t) (fun _ _ => 0) 0 0 m n
  have h' : fmhaMainloopSlabDeltaAt regs rf t m n =
      fmhaHalfDelta (fmhaSlabA rf regs.src2 t)
          (fmhaSlabB rf regs.src1 regs.src1Sub t) 0 0 0 m n +
        fmhaHalfDelta (fmhaSlabA rf regs.src2 t)
          (fmhaSlabB rf regs.src1 regs.src1Sub t) 0 0 16 m n := by
    simpa [fmhaAtom, fmhaMainloopSlabDeltaAt] using h
  rw [h']
  unfold fmhaSlabA fmhaSlabB
  rw [fmhaHalfDelta_slab, fmhaHalfDelta_slab]
  rfl

/-- The K=64 mainloop is four K=16 halves grouped as two K=32 atoms, matching
the existing `fmhaAtom_eq_sum_halves` split inside each atom. -/
theorem fmhaMainloopStepAt_two_eq_halves (regs : DpasRegs) (rf : RegFile)
    (m n : Nat) (hm : m < 8) (hn : n < 8) :
    readTileC (fmhaMainloopStepAt regs rf 2) regs.dst m n =
      readTileC rf regs.dst m n +
        (fmhaHalfDelta (readTileA rf regs.src2)
            (readTileB rf regs.src1 regs.src1Sub) 0 0 0 m n +
          fmhaHalfDelta (readTileA rf regs.src2)
            (readTileB rf regs.src1 regs.src1Sub) 0 0 16 m n) +
        (fmhaHalfDelta (readTileA rf regs.src2)
            (readTileB rf regs.src1 regs.src1Sub) 0 0 32 m n +
          fmhaHalfDelta (readTileA rf regs.src2)
            (readTileB rf regs.src1 regs.src1Sub) 0 0 48 m n) := by
  rw [fmhaMainloopStepAt_two_c regs rf m n hm hn,
    fmhaMainloopSlabDelta_eq_halves regs rf 0 m n,
    fmhaMainloopSlabDelta_eq_halves regs rf 1 m n]

/-! ## Two mainloops on disjoint C blocks -/

/-- Two mainloops on disjoint C blocks, both reading their operands and
incoming accumulators from the same `rf` snapshot. -/
def fmhaMainloopPairAt (regs1 regs2 : DpasRegs) (rf : RegFile)
    (T1 T2 : Nat) : RegFile :=
  writeTileC
    (writeTileC rf regs1.dst
      (fmhaMainloopTileAt (readTileC rf regs1.dst)
        (fmhaMainloopSlabDeltaAt regs1 rf) T1))
    regs2.dst
    (fmhaMainloopTileAt (readTileC rf regs2.dst)
      (fmhaMainloopSlabDeltaAt regs2 rf) T2)

/-- Two mainloops on disjoint C blocks commute. -/
theorem fmhaMainloopPairAt_commute {regs1 regs2 : DpasRegs} (rf : RegFile)
    (T1 T2 : Nat) (hdisj : TileCDisjoint regs1.dst regs2.dst) :
    fmhaMainloopPairAt regs1 regs2 rf T1 T2 =
      fmhaMainloopPairAt regs2 regs1 rf T2 T1 := by
  unfold fmhaMainloopPairAt
  exact writeTileC_commute_of_disjoint rf hdisj _ _

/-- The first block of a disjoint pair receives its own `dpasRun` sum. -/
theorem fmhaMainloopPairAt_first {regs1 regs2 : DpasRegs} (rf : RegFile)
    (T1 T2 m n : Nat) (hdisj : TileCDisjoint regs1.dst regs2.dst)
    (hm : m < 8) (hn : n < 8) :
    readTileC (fmhaMainloopPairAt regs1 regs2 rf T1 T2) regs1.dst m n =
      readTileC rf regs1.dst m n +
        dpasRun (readTileA rf regs1.src2)
          (readTileB rf regs1.src1 regs1.src1Sub) 0 0 32 T1
          (fun _ _ => 0) m n := by
  unfold fmhaMainloopPairAt
  rw [readTileC_writeTileC_of_disjoint (writeTileC rf regs1.dst _)
    regs1.dst regs2.dst _ hdisj m n hm hn]
  rw [readTileC_writeTileC _ regs1.dst _ m n hm hn]
  exact fmhaMainloopTileAt_dpasRun regs1 rf T1 m n

/-- The second block of a disjoint pair receives its own `dpasRun` sum. -/
theorem fmhaMainloopPairAt_second {regs1 regs2 : DpasRegs} (rf : RegFile)
    (T1 T2 m n : Nat) (hm : m < 8) (hn : n < 8) :
    readTileC (fmhaMainloopPairAt regs1 regs2 rf T1 T2) regs2.dst m n =
      readTileC rf regs2.dst m n +
        dpasRun (readTileA rf regs2.src2)
          (readTileB rf regs2.src1 regs2.src1Sub) 0 0 32 T2
          (fun _ _ => 0) m n := by
  unfold fmhaMainloopPairAt
  rw [readTileC_writeTileC _ regs2.dst _ m n hm hn]
  exact fmhaMainloopTileAt_dpasRun regs2 rf T2 m n

/-- Composition: two mainloops on disjoint C blocks commute and each block is
the incoming block plus its own `dpasRun` sum. -/
theorem fmhaMainloopPairAt_commute_and_sum {regs1 regs2 : DpasRegs}
    (rf : RegFile) (T1 T2 : Nat)
    (hdisj : TileCDisjoint regs1.dst regs2.dst) :
    (fmhaMainloopPairAt regs1 regs2 rf T1 T2 =
      fmhaMainloopPairAt regs2 regs1 rf T2 T1) ∧
    (∀ m n, m < 8 → n < 8 →
      readTileC (fmhaMainloopPairAt regs1 regs2 rf T1 T2) regs1.dst m n =
        readTileC rf regs1.dst m n +
          dpasRun (readTileA rf regs1.src2)
            (readTileB rf regs1.src1 regs1.src1Sub) 0 0 32 T1
            (fun _ _ => 0) m n) ∧
    (∀ m n, m < 8 → n < 8 →
      readTileC (fmhaMainloopPairAt regs1 regs2 rf T1 T2) regs2.dst m n =
        readTileC rf regs2.dst m n +
          dpasRun (readTileA rf regs2.src2)
            (readTileB rf regs2.src1 regs2.src1Sub) 0 0 32 T2
            (fun _ _ => 0) m n) :=
  ⟨fmhaMainloopPairAt_commute rf T1 T2 hdisj,
   fun m n hm hn => fmhaMainloopPairAt_first rf T1 T2 m n hdisj hm hn,
   fun m n hm hn => fmhaMainloopPairAt_second rf T1 T2 m n hm hn⟩

/-- The decoded C blocks `383` and `391`, each with its own mainloop. -/
theorem fmhaMainloopPairAt_383_391_commute_and_sum (rf : RegFile)
    (T1 T2 : Nat) :
    (fmhaMainloopPairAt fmhaDecodedRegs fmhaRegsC391 rf T1 T2 =
      fmhaMainloopPairAt fmhaRegsC391 fmhaDecodedRegs rf T2 T1) ∧
    (∀ m n, m < 8 → n < 8 →
      readTileC (fmhaMainloopPairAt fmhaDecodedRegs fmhaRegsC391 rf T1 T2)
          383 m n =
        readTileC rf 383 m n +
          dpasRun (readTileA rf 39) (readTileB rf 335 0) 0 0 32 T1
            (fun _ _ => 0) m n) ∧
    (∀ m n, m < 8 → n < 8 →
      readTileC (fmhaMainloopPairAt fmhaDecodedRegs fmhaRegsC391 rf T1 T2)
          391 m n =
        readTileC rf 391 m n +
          dpasRun (readTileA rf 39) (readTileB rf 335 0) 0 0 32 T2
            (fun _ _ => 0) m n) :=
  fmhaMainloopPairAt_commute_and_sum rf T1 T2 tileCDisjoint_383_391

end IntelGpu
