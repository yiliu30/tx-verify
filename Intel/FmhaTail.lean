-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.FmhaMainloop

@[expose] public section

/-!
# FMHA mainloop tail: zero-padded partial K

`Intel.FmhaMainloop` proves the `T`-step mainloop for a K tile whose depth is
exactly `T * 32`. Real FMHA depths need not be multiples of the depth-32 atom,
so the last slab is partial: only `r < 32` depth positions contribute.

This module models that tail by zero-extending the operand tiles past the true
depth `K = T * 32 + r` and issuing one more full depth-32 DPAS:

- `fmhaPadA`/`fmhaPadB` extend A and B with zeros at depth `>= K`;
- `tailSlab_eq_dotMatFrom` shows the padded tail slab is exactly the partial
  dot product over `[T * 32, T * 32 + r)`;
- `fmhaTailSlabA`/`fmhaTailSlabB` are the register-level padded operands and
  `fmhaMainloopTailStepAt` runs the `T` full slabs followed by the padded tail;
- `fmhaMainloopTail_c` identifies the C block with the incoming block plus
  `dotMat` at the true depth `K`, with `fmhaMainloopTail_c_dpasRun` giving the
  `dpasRun`-plus-tail form;
- `fmhaMainloopTail_c_zero` is the `r = 0` specialization, reducing to
  `fmhaMainloopStepAt_c_dotMat` from stage 155, and `fmhaMainloopTail_c_zero_T`
  covers `K < 32` (`T = 0`);
- `fmhaMainloopTailStepAt_frame` says every element outside the C block is
  unchanged.

## Zero-padding assumption

The padding is a value-level idealization, not a decoded hardware behavior:

- register elements at depth `>= K` are treated as zero regardless of their
  actual contents;
- masked/partial DPAS hardware behavior is not modeled. A real kernel could
  instead use a masked or predicated DPAS (where the instruction form supports
  it) or zero-fill the operand lanes before issuing a full DPAS; this module
  decodes neither choice. The full-depth DPAS over zero-extended operands is a
  value-level idealization: it proves only that *if* operand lanes at depth
  `>= K` are zero, the depth-32 instruction has the partial-dot-product value.
- zero times any `Word` is zero in the `BitVec 32` model. Floating-point
  hardware multiplication can turn `0 * NaN` into NaN, so the equivalence is
  stated for the modeled value algebra only, not for IEEE fp8 specials.

The register maps are the logical packing of `Intel.FmhaExec` and
`Intel.FmhaMainloop`; no physical dword or byte layout equivalence is asserted.
-/

namespace IntelGpu

/-! ## Zero extension of the matrix operands -/

/-- Zero-extend A past depth `K`: columns `k < K` are unchanged, columns
`k >= K` are zero. -/
def fmhaPadA (A : Nat → Nat → Word) (K : Nat) : Nat → Nat → Word :=
  fun m k => if k < K then A m k else 0

/-- Zero-extend B past depth `K`: rows `k < K` are unchanged, rows `k >= K`
are zero. -/
def fmhaPadB (B : Nat → Nat → Word) (K : Nat) : Nat → Nat → Word :=
  fun k n => if k < K then B k n else 0

theorem fmhaPadA_of_lt (A : Nat → Nat → Word) (K m k : Nat) (h : k < K) :
    fmhaPadA A K m k = A m k := by
  simp [fmhaPadA, h]

theorem fmhaPadA_of_ge (A : Nat → Nat → Word) (K m k : Nat) (h : K ≤ k) :
    fmhaPadA A K m k = 0 := by
  have h' : ¬ k < K := by omega
  simp [fmhaPadA, h']

theorem fmhaPadB_of_lt (B : Nat → Nat → Word) (K k n : Nat) (h : k < K) :
    fmhaPadB B K k n = B k n := by
  simp [fmhaPadB, h]

theorem fmhaPadB_of_ge (B : Nat → Nat → Word) (K k n : Nat) (h : K ≤ k) :
    fmhaPadB B K k n = 0 := by
  have h' : ¬ k < K := by omega
  simp [fmhaPadB, h']

/-- A slab whose left operand is pointwise zero is zero. -/
theorem dpasSlab_zero_of_left_zero (d : Nat) (A B : Nat → Nat → Word) (m n : Nat)
    (hA : ∀ k m', A k m' = 0) :
    dpasSlab d A B m n = 0 := by
  induction d generalizing A B with
  | zero => rfl
  | succ d ih =>
      rw [dpasSlab, hA 0 m]
      simpa using ih (fun k m' => A (k + 1) m') (fun k n' => B (k + 1) n')
        (fun k m' => hA (k + 1) m')

/-- A slab with a zero left operand is zero. -/
theorem dpasSlab_zero_left (d : Nat) (B : Nat → Nat → Word) (m n : Nat) :
    dpasSlab d (fun _ _ => 0) B m n = 0 :=
  dpasSlab_zero_of_left_zero d _ B m n (fun _ _ => rfl)

/-- The padded depth-`d` slab over `[t, t + r)` is the partial dot product.
The left operand vanishes at slab positions `k >= r`, because the global
depth `t + k` is then at least `t + r = K`; the same holds for the right
operand. -/
theorem dpasSlab_pad_eq_dotMatFrom (A B : Nat → Nat → Word)
    (K t r d : Nat) (hK : K = t + r) (hr : r ≤ d) (m n : Nat) :
    dpasSlab d (fun k m' => fmhaPadA A K m' (t + k))
      (fun k n' => fmhaPadB B K (t + k) n') m n =
      dotMatFrom A B m n t r := by
  have hsplit := dpasSlab_split r (d - r)
    (fun k m' => fmhaPadA A K m' (t + k))
    (fun k n' => fmhaPadB B K (t + k) n') m n
  rw [Nat.add_sub_of_le hr] at hsplit
  rw [hsplit]
  have hfirst :
      dpasSlab r (fun k m' => fmhaPadA A K m' (t + k))
        (fun k n' => fmhaPadB B K (t + k) n') m n =
      dpasSlab r (fun k m' => A (0 + m') (t + k))
        (fun k n' => B (t + k) (0 + n')) m n := by
    apply dpasSlab_congr_at r m n
    · intro k hk
      rw [fmhaPadA_of_lt A K m (t + k) (by omega), Nat.zero_add]
    · intro k hk
      rw [fmhaPadB_of_lt B K (t + k) n (by omega), Nat.zero_add]
  rw [hfirst, dpasSlab_eq_dotMatFrom A B 0 0 t r m n]
  simp only [Nat.zero_add]
  have hsecond :
      dpasSlab (d - r)
        (fun k m' => fmhaPadA A K m' (t + (k + r)))
        (fun k n' => fmhaPadB B K (t + (k + r)) n') m n = 0 := by
    have hleft : (fun k m' => fmhaPadA A K m' (t + (k + r))) = fun _ _ => 0 := by
      funext k m'
      exact fmhaPadA_of_ge A K m' (t + (k + r)) (by omega)
    rw [hleft]
    exact dpasSlab_zero_left (d - r) _ m n
  rw [hsecond]
  simp

/-- The zero-padded tail slab at slab index `T`: one full depth-32 `dpasSlab`
over the operands extended with zeros beyond `K`. -/
def fmhaTailSlab (A B : Nat → Nat → Word) (K T : Nat) : Nat → Nat → Word :=
  fun m n =>
    dpasSlab 32 (fun k m' => fmhaPadA A K m' (T * 32 + k))
      (fun k n' => fmhaPadB B K (T * 32 + k) n') m n

/-- The padded tail slab is the partial matrix dot product over
`[T * 32, T * 32 + r)`. The pads are zero for every slab position `k >= r`,
which is exactly the part cut off by `r < 32`. The statements also allow
`r = 0`, where both sides are zero; that degenerate tail is specialized in
`fmhaMainloopTail_c_zero`. -/
theorem tailSlab_eq_dotMatFrom (A B : Nat → Nat → Word) (K T r m n : Nat)
    (hK : K = T * 32 + r) (hr : r < 32) :
    fmhaTailSlab A B K T m n = dotMatFrom A B m n (T * 32) r := by
  unfold fmhaTailSlab
  exact dpasSlab_pad_eq_dotMatFrom A B K (T * 32) r 32 hK (by omega) m n

/-! ## Register-level padded operands -/

/-- A operand of the zero-padded tail slab. Depth `t * 32 + k` is read from
the register file only below the true depth `K`; at or above `K` it is zero. -/
def fmhaTailSlabA (rf : RegFile) (base K t : Nat) : Nat → Nat → Word :=
  fun m k => if t * 32 + k < K then readTileA rf base m (t * 32 + k) else 0

/-- B operand of the zero-padded tail slab. -/
def fmhaTailSlabB (rf : RegFile) (base sub K t : Nat) : Nat → Nat → Word :=
  fun k n => if t * 32 + k < K then readTileB rf base sub (t * 32 + k) n else 0

theorem fmhaTailSlabA_of_lt (rf : RegFile) (base K t m k : Nat)
    (h : t * 32 + k < K) :
    fmhaTailSlabA rf base K t m k = readTileA rf base m (t * 32 + k) := by
  simp [fmhaTailSlabA, h]

theorem fmhaTailSlabA_of_ge (rf : RegFile) (base K t m k : Nat)
    (h : K ≤ t * 32 + k) :
    fmhaTailSlabA rf base K t m k = 0 := by
  have h' : ¬ t * 32 + k < K := by omega
  simp [fmhaTailSlabA, h']

theorem fmhaTailSlabB_of_lt (rf : RegFile) (base sub K t k n : Nat)
    (h : t * 32 + k < K) :
    fmhaTailSlabB rf base sub K t k n =
      readTileB rf base sub (t * 32 + k) n := by
  simp [fmhaTailSlabB, h]

theorem fmhaTailSlabB_of_ge (rf : RegFile) (base sub K t k n : Nat)
    (h : K ≤ t * 32 + k) :
    fmhaTailSlabB rf base sub K t k n = 0 := by
  have h' : ¬ t * 32 + k < K := by omega
  simp [fmhaTailSlabB, h']

/-- The depth-32 delta of the padded tail slab, without the accumulator. -/
def fmhaTailSlabDeltaAt (regs : DpasRegs) (rf : RegFile) (K t : Nat) :
    Nat → Nat → Word :=
  fun m n => dpasSlab 32 (fun k m' => fmhaTailSlabA rf regs.src2 K t m' k)
    (fmhaTailSlabB rf regs.src1 regs.src1Sub K t) m n

/-- One full depth-32 DPAS over the padded tail slab, accumulated into the C
block of `state`. -/
def fmhaTailSlabAt (regs : DpasRegs) (rf : RegFile) (K t : Nat)
    (state : RegFile) : RegFile :=
  fmhaDpasWith regs.dst (fmhaTailSlabA rf regs.src2 K t)
    (fmhaTailSlabB rf regs.src1 regs.src1Sub K t) state

/-- Inside the C block, one tail slab step adds its padded depth-32 delta. -/
theorem fmhaTailSlabAt_c (regs : DpasRegs) (rf : RegFile) (K t : Nat)
    (state : RegFile) (m n : Nat) (hm : m < 8) (hn : n < 8) :
    readTileC (fmhaTailSlabAt regs rf K t state) regs.dst m n =
      readTileC state regs.dst m n + fmhaTailSlabDeltaAt regs rf K t m n := by
  have h := fmhaDpasWith_c regs.dst (fmhaTailSlabA rf regs.src2 K t)
    (fmhaTailSlabB rf regs.src1 regs.src1Sub K t) state m n hm hn
  simpa [fmhaTailSlabAt, fmhaAtom, fmhaTailSlabDeltaAt] using h

/-- One tail slab step leaves every element outside the C block unchanged. -/
theorem fmhaTailSlabAt_frame (regs : DpasRegs) (rf : RegFile) (K t : Nat)
    (state : RegFile) (r e : Nat) (h : ¬ inTileC regs.dst r e) :
    fmhaTailSlabAt regs rf K t state r e = state r e := by
  simpa [fmhaTailSlabAt, fmhaDpasWith] using
    writeTileC_frame state regs.dst _ r e h

/-- The padded tail delta is the partial dot product over `[T * 32, T * 32 + r)`
of the register-file operand tiles. -/
theorem fmhaTailSlabDeltaAt_eq_dotMatFrom (regs : DpasRegs) (rf : RegFile)
    (K T r m n : Nat) (hK : K = T * 32 + r) (hr : r < 32) :
    fmhaTailSlabDeltaAt regs rf K T m n =
      dotMatFrom (readTileA rf regs.src2)
        (readTileB rf regs.src1 regs.src1Sub) m n (T * 32) r := by
  unfold fmhaTailSlabDeltaAt fmhaTailSlabA fmhaTailSlabB
  exact dpasSlab_pad_eq_dotMatFrom (readTileA rf regs.src2)
    (readTileB rf regs.src1 regs.src1Sub) K (T * 32) r 32 hK (by omega) m n

/-! ## The mainloop with a padded tail -/

/-- The `T`-step mainloop followed by one padded tail slab at index `T`. -/
def fmhaMainloopTailStepAt (regs : DpasRegs) (rf : RegFile) (K T : Nat) :
    RegFile :=
  fmhaTailSlabAt regs rf K T (fmhaMainloopStepAt regs rf T)

/-- The C block after the full slabs and the padded tail is the C block after
the full slabs plus the padded tail delta. -/
theorem fmhaMainloopTailStepAt_c (regs : DpasRegs) (rf : RegFile) (K T : Nat)
    (m n : Nat) (hm : m < 8) (hn : n < 8) :
    readTileC (fmhaMainloopTailStepAt regs rf K T) regs.dst m n =
      readTileC (fmhaMainloopStepAt regs rf T) regs.dst m n +
        fmhaTailSlabDeltaAt regs rf K T m n := by
  unfold fmhaMainloopTailStepAt
  exact fmhaTailSlabAt_c regs rf K T (fmhaMainloopStepAt regs rf T) m n hm hn

/-- `dpasRun` form: the `T` full slabs contribute the depth-`T * 32`
`dpasRun`, and the last term is the padded tail delta. -/
theorem fmhaMainloopTail_c_dpasRun (regs : DpasRegs) (rf : RegFile) (K T : Nat)
    (m n : Nat) (hm : m < 8) (hn : n < 8) :
    readTileC (fmhaMainloopTailStepAt regs rf K T) regs.dst m n =
      readTileC rf regs.dst m n +
        dpasRun (readTileA rf regs.src2) (readTileB rf regs.src1 regs.src1Sub)
          0 0 32 T (fun _ _ => 0) m n +
        fmhaTailSlabDeltaAt regs rf K T m n := by
  rw [fmhaMainloopTailStepAt_c regs rf K T m n hm hn,
    fmhaMainloopStepAt_c regs rf T m n hm hn]

/-- Value form without an accumulator: the `dpasRun` sum plus the padded tail
delta is the full depth-`K` dot product. -/
theorem fmhaMainloopTail_dpasRun_add_tail (regs : DpasRegs) (rf : RegFile)
    (K T r m n : Nat) (hK : K = T * 32 + r) (hr : r < 32) :
    dpasRun (readTileA rf regs.src2) (readTileB rf regs.src1 regs.src1Sub)
        0 0 32 T (fun _ _ => 0) m n +
      fmhaTailSlabDeltaAt regs rf K T m n =
      dotMat (readTileA rf regs.src2) (readTileB rf regs.src1 regs.src1Sub)
        m n K := by
  rw [dpasRun_correct, fmhaTailSlabDeltaAt_eq_dotMatFrom regs rf K T r m n hK hr]
  rw [hK]
  simp only [dotMat, Nat.zero_add]
  rw [dotMatFrom_append (readTileA rf regs.src2)
    (readTileB rf regs.src1 regs.src1Sub) m n (T * 32) 0 r]
  simp [Nat.zero_add]

/-- Main tail law: `T` full depth-32 slabs plus the zero-padded tail equal the
incoming C block plus `dotMat` at the true depth `K = T * 32 + r`. No `0 < r`
hypothesis is needed: at `r = 0` this reduces to the stage-155 statement
`fmhaMainloopStepAt_c_dotMat` through `fmhaMainloopTail_c_zero`. -/
theorem fmhaMainloopTail_c (regs : DpasRegs) (rf : RegFile)
    (K T r m n : Nat) (hK : K = T * 32 + r) (hr : r < 32)
    (hm : m < 8) (hn : n < 8) :
    readTileC (fmhaMainloopTailStepAt regs rf K T) regs.dst m n =
      readTileC rf regs.dst m n +
        dotMat (readTileA rf regs.src2) (readTileB rf regs.src1 regs.src1Sub)
          m n K := by
  rw [fmhaMainloopTailStepAt_c regs rf K T m n hm hn,
    fmhaMainloopStepAt_c_dotMat regs rf T m n hm hn,
    fmhaTailSlabDeltaAt_eq_dotMatFrom regs rf K T r m n hK hr]
  rw [hK]
  simp only [dotMat]
  rw [dotMatFrom_append (readTileA rf regs.src2)
    (readTileB rf regs.src1 regs.src1Sub) m n (T * 32) 0 r]
  simp [Nat.zero_add, BitVec.add_assoc]

/-- Every element outside the C block is unchanged after the full slabs and
the padded tail. -/
theorem fmhaMainloopTailStepAt_frame (regs : DpasRegs) (rf : RegFile)
    (K T r e : Nat) (h : ¬ inTileC regs.dst r e) :
    fmhaMainloopTailStepAt regs rf K T r e = rf r e := by
  unfold fmhaMainloopTailStepAt
  rw [fmhaTailSlabAt_frame regs rf K T (fmhaMainloopStepAt regs rf T) r e h]
  exact fmhaMainloopStepAt_frame regs rf T r e h

/-! ## `r = 0`: the stage-155 mainloop -/

/-- With no remainder, every padded operand of the tail slab is zero. -/
theorem fmhaTailSlabA_eq_zero_of_le (rf : RegFile) (base K t : Nat)
    (h : K ≤ t * 32) :
    fmhaTailSlabA rf base K t = fun _ _ => 0 := by
  funext m k
  have h' : ¬ t * 32 + k < K := by omega
  simp [fmhaTailSlabA, h']

/-- When the slab starts at or past `K`, the padded tail slab is the identity:
its full depth-32 instruction has a zero left operand. -/
theorem fmhaTailSlabAt_eq_self (regs : DpasRegs) (rf : RegFile) (K t : Nat)
    (state : RegFile) (h : K ≤ t * 32) :
    fmhaTailSlabAt regs rf K t state = state := by
  unfold fmhaTailSlabAt fmhaDpasWith
  rw [fmhaTailSlabA_eq_zero_of_le rf regs.src2 K t h]
  have hC : fmhaAtom (fun _ _ => 0)
        (fmhaTailSlabB rf regs.src1 regs.src1Sub K t)
        (readTileC state regs.dst) 0 0 = readTileC state regs.dst := by
    funext m n
    unfold fmhaAtom
    simp only [Nat.zero_add]
    rw [dpasSlab_zero_of_left_zero 32 _ _ m n (fun _ _ => rfl)]
    simp
  rw [hC, writeTileC_readTileC]

/-- `r = 0` specialization: the padded tail is a no-op, so the tail mainloop
is exactly the stage-155 `T`-step mainloop. -/
theorem fmhaMainloopTailStepAt_zero_eq_stepAt (regs : DpasRegs) (rf : RegFile)
    (T : Nat) :
    fmhaMainloopTailStepAt regs rf (T * 32) T = fmhaMainloopStepAt regs rf T := by
  unfold fmhaMainloopTailStepAt
  exact fmhaTailSlabAt_eq_self regs rf (T * 32) T
    (fmhaMainloopStepAt regs rf T) (Nat.le_refl _)

/-- `r = 0` value form: the C block is the stage-155 depth-`T * 32` result. -/
theorem fmhaMainloopTail_c_zero (regs : DpasRegs) (rf : RegFile) (T m n : Nat)
    (hm : m < 8) (hn : n < 8) :
    readTileC (fmhaMainloopTailStepAt regs rf (T * 32) T) regs.dst m n =
      readTileC rf regs.dst m n +
        dotMat (readTileA rf regs.src2) (readTileB rf regs.src1 regs.src1Sub)
          m n (T * 32) := by
  rw [fmhaMainloopTailStepAt_zero_eq_stepAt]
  exact fmhaMainloopStepAt_c_dotMat regs rf T m n hm hn

/-! ## `T = 0`: a depth below one atom -/

/-- `T = 0` specialization: the padded tail is the whole mainloop. -/
theorem fmhaMainloopTailStepAt_zero_T_eq (regs : DpasRegs) (rf : RegFile)
    (K : Nat) :
    fmhaMainloopTailStepAt regs rf K 0 = fmhaTailSlabAt regs rf K 0 rf := by
  unfold fmhaMainloopTailStepAt
  rw [fmhaMainloopStepAt_zero]

/-- `T = 0` value form for `K < 32`: one padded depth-32 DPAS is the full
depth-`K` dot product. -/
theorem fmhaMainloopTail_c_zero_T (regs : DpasRegs) (rf : RegFile) (K m n : Nat)
    (hK : K < 32) (hm : m < 8) (hn : n < 8) :
    readTileC (fmhaMainloopTailStepAt regs rf K 0) regs.dst m n =
      readTileC rf regs.dst m n +
        dotMat (readTileA rf regs.src2) (readTileB rf regs.src1 regs.src1Sub)
          m n K := by
  have hK' : K = 0 * 32 + K := by omega
  simpa using fmhaMainloopTail_c regs rf K 0 K m n hK' hK hm hn

end IntelGpu
