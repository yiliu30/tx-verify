-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.FmhaAtomTile

@[expose] public section

/-!
# Register-level execution of the decoded FMHA DPAS

`Intel.RealDpas` decodes the FMHA instruction

```
dpas.8x8 (16|M0) r383:f null:f r39:hf8 r335.0:hf8 {Atomic,Fwd,$6.dst}
```

to the 8x8x32 fp8 atom `fmhaFp8Atom` with accumulator base `r383`, B base
`r335.0` and A base `r39`. `Intel.FmhaAtomTile` proves the value-level atom
algebra. This module moves one atom to a register-file execution step:

- `RegFile` maps a register number and an element index to a `Word`;
- `readTileA`, `readTileB` and `readTileC` read the atom's operand and
  accumulator tiles, and `writeTileC` writes the 8x8 accumulator block;
- `fmhaDpasStep` reads A, B and C at the decoded bases, applies `fmhaAtom`,
  and writes the result back to the C block;
- `fmhaDpasStep_c` and `fmhaDpasStep_atom` identify the C block after the
  step with `fmhaAtom` and with `C + dotMat ... 32`;
- `fmhaDpasStep_frame` says every register element outside the C block is
  unchanged;
- `fmhaDpasStep_decoded` specializes the step to `⟨383, 335, 0, 39⟩` and
  connects that tuple to `realFmhaDpas_regs`;
- `fmhaDpasStepAt_383_391_commute_and_sum` composes two atoms on the disjoint
  C blocks `383` and `383 + 8`, proving that the steps commute and that each
  block receives the pointwise original accumulator plus its depth-32 dot.

## Modelled register packing

The dump fixes the operand bases but not the complete per-element register
layout. This module therefore uses one explicit, purely logical word-tile
layout for the atom:

- A element `(m, k)` is `rf (A + k) m`;
- B element `(k, n)` is `rf (B + n) (sub + k)`;
- C element `(m, n)` is `rf (C + m) n`.

Thus the C block occupies registers `C .. C + 7` and elements `0 .. 7`, and A
and B are depth-major and column-major respectively. These address maps are a
model assumption, not a decoded claim about the compiled kernel's physical
dword or byte lanes. `Intel.DpasPacking` models the ISA's packed fp8 byte
layout separately; this module does not assert that the two layouts coincide.
The decoded bases and the 8x8x32 shape are the facts carried over from the
instruction.
-/

namespace IntelGpu

/-- A register file indexed by register number and element index. -/
abbrev RegFile := Nat → Nat → Word

/-- Logical A tile: depth `k` selects register `base + k`, row `m` selects the
element. This is the module's modelled A layout. -/
def readTileA (rf : RegFile) (base : Nat) : Nat → Nat → Word :=
  fun m k => rf (base + k) m

/-- Logical B tile: column `n` selects register `base + n`, depth `k` selects
element `sub + k`. This is the module's modelled B layout. -/
def readTileB (rf : RegFile) (base sub : Nat) : Nat → Nat → Word :=
  fun k n => rf (base + n) (sub + k)

/-- Logical 8x8 C tile: row `m` selects register `base + m`, column `n`
selects the element. -/
def readTileC (rf : RegFile) (base : Nat) : Nat → Nat → Word :=
  fun m n => rf (base + m) n

/-- The modelled footprint of an 8x8 C block. -/
def inTileC (base r e : Nat) : Prop :=
  base ≤ r ∧ r < base + 8 ∧ e < 8

instance (base r e : Nat) : Decidable (inTileC base r e) := by
  unfold inTileC
  infer_instance

/-- Write an 8x8 logical C tile into the register file. Elements outside the
block are framed. -/
def writeTileC (rf : RegFile) (base : Nat) (C : Nat → Nat → Word) : RegFile :=
  fun r e => if inTileC base r e then C (r - base) e else rf r e

/-- Two C blocks are disjoint when they share no register element. -/
def TileCDisjoint (base1 base2 : Nat) : Prop :=
  ∀ r e, ¬ (inTileC base1 r e ∧ inTileC base2 r e)

theorem TileCDisjoint_symm {base1 base2 : Nat} (h : TileCDisjoint base1 base2) :
    TileCDisjoint base2 base1 := by
  intro r e h'
  exact h r e ⟨h'.2, h'.1⟩

theorem writeTileC_frame (rf : RegFile) (base : Nat) (C : Nat → Nat → Word)
    (r e : Nat) (h : ¬ inTileC base r e) :
    writeTileC rf base C r e = rf r e := by
  simp [writeTileC, h]

theorem readTileC_writeTileC (rf : RegFile) (base : Nat)
    (C : Nat → Nat → Word) (m n : Nat) (hm : m < 8) (hn : n < 8) :
    readTileC (writeTileC rf base C) base m n = C m n := by
  unfold readTileC writeTileC inTileC
  have hle : base ≤ base + m := Nat.le_add_right base m
  have hlt : base + m < base + 8 := by omega
  simp [hle, hlt, hn, Nat.add_sub_cancel_left]

theorem readTileC_writeTileC_of_disjoint (rf : RegFile) (readBase writeBase : Nat)
    (C : Nat → Nat → Word) (hdisj : TileCDisjoint readBase writeBase)
    (m n : Nat) (hm : m < 8) (hn : n < 8) :
    readTileC (writeTileC rf writeBase C) readBase m n =
      readTileC rf readBase m n := by
  unfold readTileC
  have hnot : ¬ inTileC writeBase (readBase + m) n := by
    intro h
    have hread : inTileC readBase (readBase + m) n := by
      unfold inTileC
      exact ⟨Nat.le_add_right readBase m, by omega, hn⟩
    exact hdisj (readBase + m) n ⟨hread, h⟩
  exact writeTileC_frame rf writeBase C (readBase + m) n hnot

theorem writeTileC_congr_on_block (rf : RegFile) (base : Nat)
    {C C' : Nat → Nat → Word}
    (h : ∀ m n, m < 8 → n < 8 → C m n = C' m n) :
    writeTileC rf base C = writeTileC rf base C' := by
  funext r e
  unfold writeTileC
  by_cases hin : inTileC base r e
  · rw [ite_eq_left hin, ite_eq_left hin]
    exact h (r - base) e (by unfold inTileC at hin; omega) hin.2.2
  · rw [ite_eq_right hin, ite_eq_right hin]

/-- Pointwise equality of depth-32 slabs at fixed output coordinates. -/
theorem dpasSlab_congr_at (d : Nat) {A A' B B' : Nat → Nat → Word} (m n : Nat)
    (hA : ∀ k, k < d → A k m = A' k m)
    (hB : ∀ k, k < d → B k n = B' k n) :
    dpasSlab d A B m n = dpasSlab d A' B' m n := by
  induction d generalizing A A' B B' with
  | zero => rfl
  | succ d ih =>
      rw [dpasSlab, dpasSlab, hA 0 (Nat.zero_lt_succ d),
        hB 0 (Nat.zero_lt_succ d)]
      congr 1
      apply ih
      · intro k _
        exact hA (k + 1) (by omega)
      · intro k _
        exact hB (k + 1) (by omega)

theorem fmhaAtom_congr (A A' B B' C C' : Nat → Nat → Word) (m n : Nat)
    (hA : ∀ k, k < 32 → A m k = A' m k)
    (hB : ∀ k, k < 32 → B k n = B' k n)
    (hC : C m n = C' m n) :
    fmhaAtom A B C 0 0 m n = fmhaAtom A' B' C' 0 0 m n := by
  unfold fmhaAtom
  simp only [Nat.zero_add]
  rw [hC, dpasSlab_congr_at 32 (A := fun k m' => A m' k)
    (A' := fun k m' => A' m' k)
    (B := fun k n' => B k n')
    (B' := fun k n' => B' k n') m n hA hB]

/-- One atom into an explicit C block: read the incoming C tile, add the atom
delta, and write the block back. -/
def fmhaDpasWith (cBase : Nat) (A B : Nat → Nat → Word) (rf : RegFile) : RegFile :=
  writeTileC rf cBase (fmhaAtom A B (readTileC rf cBase) 0 0)

theorem fmhaDpasWith_c (cBase : Nat) (A B : Nat → Nat → Word) (rf : RegFile)
    (m n : Nat) (hm : m < 8) (hn : n < 8) :
    readTileC (fmhaDpasWith cBase A B rf) cBase m n =
      fmhaAtom A B (readTileC rf cBase) 0 0 m n := by
  simpa [fmhaDpasWith] using readTileC_writeTileC rf cBase _ m n hm hn

theorem fmhaDpasWith_atom (cBase : Nat) (A B : Nat → Nat → Word) (rf : RegFile)
    (m n : Nat) (hm : m < 8) (hn : n < 8) :
    readTileC (fmhaDpasWith cBase A B rf) cBase m n =
      readTileC rf cBase m n + dotMat A B m n 32 := by
  rw [fmhaDpasWith_c cBase A B rf m n hm hn]
  have h := fmhaAtom_correct A B (readTileC rf cBase) 0 0 m n
  simpa [dotMat] using h

theorem writeTileC_commute_of_disjoint (rf : RegFile) {base1 base2 : Nat}
    (hdisj : TileCDisjoint base1 base2) (C1 C2 : Nat → Nat → Word) :
    writeTileC (writeTileC rf base1 C1) base2 C2 =
      writeTileC (writeTileC rf base2 C2) base1 C1 := by
  funext r e
  unfold writeTileC
  by_cases h1 : inTileC base1 r e
  · have h2 : ¬ inTileC base2 r e := fun h2 => hdisj r e ⟨h1, h2⟩
    simp [h1, h2]
  · by_cases h2 : inTileC base2 r e
    · simp [h1, h2]
    · simp [h1, h2]

theorem fmhaDpasWith_commute_of_disjoint {base1 base2 : Nat}
    (hdisj : TileCDisjoint base1 base2) (A1 B1 A2 B2 : Nat → Nat → Word)
    (rf : RegFile) :
    fmhaDpasWith base2 A2 B2 (fmhaDpasWith base1 A1 B1 rf) =
      fmhaDpasWith base1 A1 B1 (fmhaDpasWith base2 A2 B2 rf) := by
  let C1 := fmhaAtom A1 B1 (readTileC rf base1) 0 0
  let C2 := fmhaAtom A2 B2 (readTileC rf base2) 0 0
  have hleft :
      fmhaDpasWith base2 A2 B2 (fmhaDpasWith base1 A1 B1 rf) =
        writeTileC (writeTileC rf base1 C1) base2 C2 := by
    unfold fmhaDpasWith
    apply writeTileC_congr_on_block
    intro m n hm hn
    apply fmhaAtom_congr A2 A2 B2 B2
    · intro k _; rfl
    · intro k _; rfl
    · exact readTileC_writeTileC_of_disjoint rf base2 base1 C1
        (TileCDisjoint_symm hdisj) m n hm hn
  have hright :
      fmhaDpasWith base1 A1 B1 (fmhaDpasWith base2 A2 B2 rf) =
        writeTileC (writeTileC rf base2 C2) base1 C1 := by
    unfold fmhaDpasWith
    apply writeTileC_congr_on_block
    intro m n hm hn
    apply fmhaAtom_congr A1 A1 B1 B1
    · intro k _; rfl
    · intro k _; rfl
    · exact readTileC_writeTileC_of_disjoint rf base1 base2 C2 hdisj m n hm hn
  rw [hleft, hright]
  exact writeTileC_commute_of_disjoint rf hdisj C1 C2

theorem fmhaDpasWith_twoAtoms_first {base1 base2 : Nat}
    (hdisj : TileCDisjoint base1 base2) (A1 B1 A2 B2 : Nat → Nat → Word)
    (rf : RegFile) (m n : Nat) (hm : m < 8) (hn : n < 8) :
    readTileC (fmhaDpasWith base2 A2 B2 (fmhaDpasWith base1 A1 B1 rf))
        base1 m n =
      readTileC rf base1 m n + dotMat A1 B1 m n 32 := by
  unfold fmhaDpasWith
  rw [readTileC_writeTileC_of_disjoint (writeTileC rf base1 (fmhaAtom A1 B1
    (readTileC rf base1) 0 0)) base1 base2 _ hdisj m n hm hn]
  rw [readTileC_writeTileC rf base1 _ m n hm hn]
  have h := fmhaAtom_correct A1 B1 (readTileC rf base1) 0 0 m n
  simpa [dotMat] using h

theorem fmhaDpasWith_twoAtoms_second {base1 base2 : Nat}
    (hdisj : TileCDisjoint base1 base2) (A1 B1 A2 B2 : Nat → Nat → Word)
    (rf : RegFile) (m n : Nat) (hm : m < 8) (hn : n < 8) :
    readTileC (fmhaDpasWith base2 A2 B2 (fmhaDpasWith base1 A1 B1 rf))
        base2 m n =
      readTileC rf base2 m n + dotMat A2 B2 m n 32 := by
  unfold fmhaDpasWith
  rw [readTileC_writeTileC (writeTileC rf base1 (fmhaAtom A1 B1
    (readTileC rf base1) 0 0)) base2 _ m n hm hn]
  have hcongr :
      fmhaAtom A2 B2 (readTileC (writeTileC rf base1 (fmhaAtom A1 B1
        (readTileC rf base1) 0 0)) base2) 0 0 m n =
        fmhaAtom A2 B2 (readTileC rf base2) 0 0 m n := by
    apply fmhaAtom_congr A2 A2 B2 B2
    · intro k _; rfl
    · intro k _; rfl
    · exact readTileC_writeTileC_of_disjoint rf base2 base1 _
        (TileCDisjoint_symm hdisj) m n hm hn
  rw [hcongr]
  have h := fmhaAtom_correct A2 B2 (readTileC rf base2) 0 0 m n
  simpa [dotMat] using h

theorem tileCDisjoint_self_add_eight (base : Nat) : TileCDisjoint base (base + 8) := by
  intro r e h
  unfold inTileC at h
  omega

theorem tileCDisjoint_383_391 : TileCDisjoint 383 391 := by
  simpa using tileCDisjoint_self_add_eight 383

theorem readTileA_writeTileC_below (rf : RegFile) (C : Nat → Nat → Word)
    (readBase writeBase m k : Nat) (h : readBase + k < writeBase) :
    readTileA (writeTileC rf writeBase C) readBase m k =
      readTileA rf readBase m k := by
  unfold readTileA writeTileC inTileC
  have hnot : ¬ (writeBase ≤ readBase + k ∧
      readBase + k < writeBase + 8 ∧ m < 8) := by
    omega
  simp [hnot]

theorem readTileB_writeTileC_below (rf : RegFile) (C : Nat → Nat → Word)
    (readBase sub writeBase k n : Nat) (h : readBase + n < writeBase) :
    readTileB (writeTileC rf writeBase C) readBase sub k n =
      readTileB rf readBase sub k n := by
  unfold readTileB writeTileC inTileC
  have hnot : ¬ (writeBase ≤ readBase + n ∧
      readBase + n < writeBase + 8 ∧ sub + k < 8) := by
    omega
  simp [hnot]

theorem fmhaDpasWith_twoAtoms_commute_and_sum {base1 base2 : Nat}
    (hdisj : TileCDisjoint base1 base2) (A1 B1 A2 B2 : Nat → Nat → Word)
    (rf : RegFile) :
    (fmhaDpasWith base2 A2 B2 (fmhaDpasWith base1 A1 B1 rf) =
      fmhaDpasWith base1 A1 B1 (fmhaDpasWith base2 A2 B2 rf)) ∧
    (∀ m n, m < 8 → n < 8 →
      readTileC (fmhaDpasWith base2 A2 B2 (fmhaDpasWith base1 A1 B1 rf))
          base1 m n =
        readTileC rf base1 m n + dotMat A1 B1 m n 32) ∧
    (∀ m n, m < 8 → n < 8 →
      readTileC (fmhaDpasWith base2 A2 B2 (fmhaDpasWith base1 A1 B1 rf))
          base2 m n =
        readTileC rf base2 m n + dotMat A2 B2 m n 32) :=
  ⟨fmhaDpasWith_commute_of_disjoint hdisj A1 B1 A2 B2 rf,
   fmhaDpasWith_twoAtoms_first hdisj A1 B1 A2 B2 rf,
   fmhaDpasWith_twoAtoms_second hdisj A1 B1 A2 B2 rf⟩

theorem fmhaDpasWith_383_391_commute_and_sum (A B : Nat → Nat → Word)
    (rf : RegFile) :
    (fmhaDpasWith 391 A B (fmhaDpasWith 383 A B rf) =
      fmhaDpasWith 383 A B (fmhaDpasWith 391 A B rf)) ∧
    (∀ m n, m < 8 → n < 8 →
      readTileC (fmhaDpasWith 391 A B (fmhaDpasWith 383 A B rf)) 383 m n =
        readTileC rf 383 m n + dotMat A B m n 32) ∧
    (∀ m n, m < 8 → n < 8 →
      readTileC (fmhaDpasWith 391 A B (fmhaDpasWith 383 A B rf)) 391 m n =
        readTileC rf 391 m n + dotMat A B m n 32) :=
  fmhaDpasWith_twoAtoms_commute_and_sum tileCDisjoint_383_391 A B A B rf

/-- Execute one decoded DPAS on a register file. The A operand is read from
`src2`, B from `src1` plus `src1Sub`, and the accumulator from `dst`. -/
def fmhaDpasStepAt (regs : DpasRegs) (rf : RegFile) : RegFile :=
  fmhaDpasWith regs.dst (readTileA rf regs.src2)
    (readTileB rf regs.src1 regs.src1Sub) rf

theorem fmhaDpasStepAt_c (regs : DpasRegs) (rf : RegFile) (m n : Nat)
    (hm : m < 8) (hn : n < 8) :
    readTileC (fmhaDpasStepAt regs rf) regs.dst m n =
      fmhaAtom (readTileA rf regs.src2) (readTileB rf regs.src1 regs.src1Sub)
        (readTileC rf regs.dst) 0 0 m n := by
  simpa [fmhaDpasStepAt] using
    fmhaDpasWith_c regs.dst (readTileA rf regs.src2)
      (readTileB rf regs.src1 regs.src1Sub) rf m n hm hn

theorem fmhaDpasStepAt_atom (regs : DpasRegs) (rf : RegFile) (m n : Nat)
    (hm : m < 8) (hn : n < 8) :
    readTileC (fmhaDpasStepAt regs rf) regs.dst m n =
      readTileC rf regs.dst m n +
        dotMat (readTileA rf regs.src2)
          (readTileB rf regs.src1 regs.src1Sub) m n 32 := by
  simpa [fmhaDpasStepAt] using
    fmhaDpasWith_atom regs.dst (readTileA rf regs.src2)
      (readTileB rf regs.src1 regs.src1Sub) rf m n hm hn

theorem fmhaDpasStepAt_frame (regs : DpasRegs) (rf : RegFile) (r e : Nat)
    (h : ¬ inTileC regs.dst r e) :
    fmhaDpasStepAt regs rf r e = rf r e := by
  simpa [fmhaDpasStepAt, fmhaDpasWith] using
    writeTileC_frame rf regs.dst _ r e h

/-- The bases decoded from the real FMHA DPAS line. -/
def fmhaDecodedRegs : DpasRegs := ⟨383, 335, 0, 39⟩

/-- The second accumulator tile starts eight registers after the first. -/
def fmhaRegsC391 : DpasRegs := ⟨391, 335, 0, 39⟩

/-- One register-level FMHA DPAS at the decoded operand bases. -/
def fmhaDpasStep (rf : RegFile) : RegFile :=
  fmhaDpasStepAt fmhaDecodedRegs rf

theorem fmhaDpasStep_eq_decoded :
    fmhaDpasStep = fmhaDpasStepAt ⟨383, 335, 0, 39⟩ := rfl

theorem fmhaDpasStepAt_383_eq (rf : RegFile) :
    fmhaDpasStepAt fmhaDecodedRegs rf =
      fmhaDpasWith 383 (readTileA rf 39) (readTileB rf 335 0) rf := rfl

theorem fmhaDpasStep_c (rf : RegFile) (m n : Nat) (hm : m < 8) (hn : n < 8) :
    readTileC (fmhaDpasStep rf) 383 m n =
      fmhaAtom (readTileA rf 39) (readTileB rf 335 0) (readTileC rf 383)
        0 0 m n := by
  simpa [fmhaDpasStep, fmhaDecodedRegs] using
    fmhaDpasStepAt_c fmhaDecodedRegs rf m n hm hn

theorem fmhaDpasStep_atom (rf : RegFile) (m n : Nat) (hm : m < 8)
    (hn : n < 8) :
    readTileC (fmhaDpasStep rf) 383 m n =
      readTileC rf 383 m n +
        dotMat (readTileA rf 39) (readTileB rf 335 0) m n 32 := by
  simpa [fmhaDpasStep, fmhaDecodedRegs] using
    fmhaDpasStepAt_atom fmhaDecodedRegs rf m n hm hn

theorem fmhaDpasStep_frame (rf : RegFile) (r e : Nat) (h : ¬ inTileC 383 r e) :
    fmhaDpasStep rf r e = rf r e := by
  simpa [fmhaDpasStep, fmhaDecodedRegs] using
    fmhaDpasStepAt_frame fmhaDecodedRegs rf r e h

theorem fmhaDpasStep_decoded :
    fmhaDpasStep = fmhaDpasStepAt ⟨383, 335, 0, 39⟩ ∧
      parseDpasRegs "r383:f" "r335.0:hf8" "r39:hf8" =
        some ⟨383, 335, 0, 39⟩ :=
  ⟨rfl, realFmhaDpas_regs⟩

theorem fmhaDpasStepAt_391_of_383 (rf : RegFile) :
    fmhaDpasStepAt fmhaRegsC391 (fmhaDpasStepAt fmhaDecodedRegs rf) =
      fmhaDpasWith 391 (readTileA rf 39) (readTileB rf 335 0)
        (fmhaDpasStepAt fmhaDecodedRegs rf) := by
  unfold fmhaDpasStepAt fmhaRegsC391 fmhaDecodedRegs fmhaDpasWith
  apply writeTileC_congr_on_block
  intro m n hm hn
  apply fmhaAtom_congr _ _ _ _ _ _
  · intro k hk
    simpa using readTileA_writeTileC_below rf _ 39 383 m k (by omega)
  · intro k hk
    simpa using readTileB_writeTileC_below rf _ 335 0 383 k n (by omega)
  · simp

theorem fmhaDpasStepAt_383_of_391 (rf : RegFile) :
    fmhaDpasStepAt fmhaDecodedRegs (fmhaDpasStepAt fmhaRegsC391 rf) =
      fmhaDpasWith 383 (readTileA rf 39) (readTileB rf 335 0)
        (fmhaDpasStepAt fmhaRegsC391 rf) := by
  unfold fmhaDpasStepAt fmhaRegsC391 fmhaDecodedRegs fmhaDpasWith
  apply writeTileC_congr_on_block
  intro m n hm hn
  apply fmhaAtom_congr _ _ _ _ _ _
  · intro k hk
    simpa using readTileA_writeTileC_below rf _ 39 391 m k (by omega)
  · intro k hk
    simpa using readTileB_writeTileC_below rf _ 335 0 391 k n (by omega)
  · simp

theorem fmhaDpasStepAt_383_391_commute (rf : RegFile) :
    fmhaDpasStepAt fmhaRegsC391 (fmhaDpasStepAt fmhaDecodedRegs rf) =
      fmhaDpasStepAt fmhaDecodedRegs (fmhaDpasStepAt fmhaRegsC391 rf) := by
  rw [fmhaDpasStepAt_391_of_383, fmhaDpasStepAt_383_of_391]
  exact (fmhaDpasWith_383_391_commute_and_sum (readTileA rf 39)
    (readTileB rf 335 0) rf).1

theorem fmhaDpasStepAt_383_391_commute_and_sum (rf : RegFile) :
    (fmhaDpasStepAt fmhaRegsC391 (fmhaDpasStepAt fmhaDecodedRegs rf) =
      fmhaDpasStepAt fmhaDecodedRegs (fmhaDpasStepAt fmhaRegsC391 rf)) ∧
    (∀ m n, m < 8 → n < 8 →
      readTileC (fmhaDpasStepAt fmhaRegsC391 (fmhaDpasStepAt fmhaDecodedRegs rf))
          383 m n =
        readTileC rf 383 m n +
          dotMat (readTileA rf 39) (readTileB rf 335 0) m n 32) ∧
    (∀ m n, m < 8 → n < 8 →
      readTileC (fmhaDpasStepAt fmhaRegsC391 (fmhaDpasStepAt fmhaDecodedRegs rf))
          391 m n =
        readTileC rf 391 m n +
          dotMat (readTileA rf 39) (readTileB rf 335 0) m n 32) := by
  refine ⟨fmhaDpasStepAt_383_391_commute rf, ?_, ?_⟩
  · intro m n hm hn
    rw [fmhaDpasStepAt_391_of_383, fmhaDpasStepAt_383_eq]
    exact (fmhaDpasWith_383_391_commute_and_sum (readTileA rf 39)
      (readTileB rf 335 0) rf).2.1 m n hm hn
  · intro m n hm hn
    rw [fmhaDpasStepAt_391_of_383, fmhaDpasStepAt_383_eq]
    exact (fmhaDpasWith_383_391_commute_and_sum (readTileA rf 39)
      (readTileB rf 335 0) rf).2.2 m n hm hn

end IntelGpu
