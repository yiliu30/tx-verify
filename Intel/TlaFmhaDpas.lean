-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaDpasExec
public import Intel.TlaMovDecode
public import Intel.Examples.RealFmhaPrefill

@[expose] public section

/-!
# FMHA prefill DPAS atoms

The prefill dump has 64 `dpas.8x8 (16|M0)` instructions. Their second
accumulator is either `null` (4 forms) or the same register block as the
first (60 forms), so every one of them accumulates once into `acc0`. This
module decodes that shape, splits the atoms into the 32 QK^T and 32 PV
atoms, and gives the single-accumulator step its slab value and frame.

The chain composition over the whole phase is the next stage.
-/

namespace IntelGpu

/-- An FMHA DPAS: `acc1 = none` is the printed `null`. -/
structure FmhaDpas where
  acc0 : Nat
  acc1 : Option Nat
  srcB : Nat
  srcA : Nat
  deriving Repr, DecidableEq

/-- Parse either a register base or `null` for the second accumulator. -/
def parseDpasRegOpt (s : String) : Option (Option Nat) :=
  if isNullOperand s then some none
  else
    match parseDpasReg s with
    | some (n, _) => some (some n)
    | none => none

def parseFmhaDpas : TlaInstr → Option FmhaDpas
  | .dpas _ d0 d1 b a _ =>
      match parseDpasReg d0, parseDpasRegOpt d1, parseDpasReg b, parseDpasReg a with
      | some (r0, _), some r1, some (rb, _), some (ra, _) =>
          some ⟨r0, r1, rb, ra⟩
      | _, _, _, _ => none
  | _ => none

/-- The 64 DPAS atoms of the prefill dump. -/
def fmhaDpas : List FmhaDpas :=
  (decodeTlaProgram realFmhaPrefill).filterMap parseFmhaDpas

set_option maxRecDepth 1000000 in
theorem fmhaDpas_length : fmhaDpas.length = 64 := by decide

set_option maxRecDepth 1000000 in
/-- 4 atoms print `null` as the second accumulator. -/
theorem fmhaDpas_null_count :
    (fmhaDpas.filter (fun d => d.acc1 = none)).length = 4 := by decide

set_option maxRecDepth 1000000 in
/-- 60 atoms alias the second accumulator to the first. -/
theorem fmhaDpas_alias_count :
    (fmhaDpas.filter (fun d => d.acc1 = some d.acc0)).length = 60 := by decide

set_option maxRecDepth 1000000 in
/-- Every atom is either `null` or aliased. -/
theorem fmhaDpas_acc1_ok :
    fmhaDpas.all (fun d => d.acc1 = none || d.acc1 = some d.acc0) = true := by
  decide

/-- The QK^T atoms accumulate into `r42..r66`. -/
def qkDpas : List FmhaDpas := fmhaDpas.filter (fun d => d.acc0 ≤ 66)

/-- The PV atoms accumulate into `r74..r194`. -/
def pvDpas : List FmhaDpas := fmhaDpas.filter (fun d => 66 < d.acc0)

set_option maxRecDepth 1000000 in
theorem qkDpas_length : qkDpas.length = 32 := by decide

set_option maxRecDepth 1000000 in
theorem pvDpas_length : pvDpas.length = 32 := by decide

/-- Execute one atom: one slab into the first accumulator. -/
def fmhaAtomStep (rf : RegFile) (d : FmhaDpas) : RegFile :=
  let A := readTileA rf d.srcA
  let B := readTileB rf d.srcB 0
  let C := readTileC rf d.acc0
  writeTileC rf d.acc0 (tlaSlab A B C)

/-- The first accumulator after one atom is the slab value. -/
theorem fmhaAtomStep_acc0 (rf : RegFile) (d : FmhaDpas) (m n : Nat)
    (hm : m < 8) (hn : n < 8) :
    readTileC (fmhaAtomStep rf d) d.acc0 m n =
      tlaSlab (readTileA rf d.srcA) (readTileB rf d.srcB 0) (readTileC rf d.acc0) m n := by
  unfold fmhaAtomStep
  exact readTileC_writeTileC rf d.acc0 _ m n hm hn

/-- An atom frames registers outside its accumulator block. -/
theorem fmhaAtomStep_frame (rf : RegFile) (d : FmhaDpas) (r e : Nat)
    (h : ¬ inTileC d.acc0 r e) : fmhaAtomStep rf d r e = rf r e := by
  unfold fmhaAtomStep
  exact writeTileC_frame rf d.acc0 _ r e h

/-- The second accumulator is irrelevant once it is `null` or aliased. -/
theorem fmhaAtomStep_acc1_irrelevant (rf : RegFile) (d : FmhaDpas) (a1 : Option Nat) :
    fmhaAtomStep rf { d with acc1 := a1 } = fmhaAtomStep rf d := rfl

end IntelGpu
