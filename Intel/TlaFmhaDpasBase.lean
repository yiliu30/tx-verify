-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaDpasExec
public import Intel.TlaDpasBf16
public import Intel.TlaMovDecode

@[expose] public section

/-!
# FMHA DPAS atoms: shape and semantics

An FMHA `dpas.8x8` prints either `null` or the same block as the first
accumulator in its second accumulator slot, so it accumulates once. This
lightweight module holds the type, parser and single-accumulator step; the
dump-specific atom list lives in `Intel/TlaFmhaDpas`.
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

/-- The packed-BF16 slab of one FMHA atom. -/
def fmhaBf16Slab (rf : RegFile) (d : FmhaDpas) (m n : Nat) : Word :=
  dpasSlab 16 (bf16ReadA rf d.srcA) (bf16ReadB rf d.srcB) m n

/-- Execute one atom: one packed-BF16 slab into the first accumulator. -/
def fmhaAtomStep (rf : RegFile) (d : FmhaDpas) : RegFile :=
  writeTileC rf d.acc0 (fun m n => readTileC rf d.acc0 m n + fmhaBf16Slab rf d m n)

/-- The first accumulator after one atom is the packed-BF16 slab value. -/
theorem fmhaAtomStep_acc0 (rf : RegFile) (d : FmhaDpas) (m n : Nat)
    (hm : m < 8) (hn : n < 8) :
    readTileC (fmhaAtomStep rf d) d.acc0 m n =
      readTileC rf d.acc0 m n + fmhaBf16Slab rf d m n := by
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
