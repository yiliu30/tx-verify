-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.DpasAtom
public import Intel.RealDecode

@[expose] public section

/-!
# A real DPAS instruction from the compiled FMHA kernel

The existing DPAS model is the SYCL-TLA 8x16x16 atom and its 16+16 depth split
(`dpasSlab_two_atoms`). This module checks that mapping against a real IGC
instruction:

```
dpas.8x8 (16|M0) r383:f null:f r39:hf8 r335.0:hf8 {Atomic,Fwd,$6.dst}
```

The compiled FMHA kernel uses an **8x8** DPAS with `hf8` sources and an `f32`
accumulator, at execution size 16. For `hf8` the ISA depth is 32, so this is one
8x8x32 atom, not an 8x16x16 atom and not the 16+16 split of `dpasSlab_two_atoms`.

## Provenance

- source: the final IGC assembly for an fmha fp8 kernel (oneAPI 2026.1 IGC)
- sha256 of the unredacted assembly:
  `b0449b8cd426dab43226bdb070da40938420c0c614c37695b32a5d676b9a85a3`
- **redacted**: the assembly's platform and options lines, which name a product.

## What is claimed

`realFmhaDpas_form` decodes the instruction text to
`⟨8x8, exec 16, hf8, f32⟩`, and `fmhaDpas_not_tlaAtom` proves that shape is not
the model's `m8n16` atom. `fmhaDpas_depth` records the 32-deep fp8 atom. The
8x16x16 two-atom theorem therefore stays scoped to the SYCL-TLA fp16/fp32
configuration; the fp8 FMHA path needs its own 8x8x32 atom.
-/

namespace IntelGpu

/-- Data types on DPAS operands. -/
inductive DpasType where
  | f32
  | hf8
  | f16
  | bf16
  deriving Repr, DecidableEq

/-- The mnemonic shapes seen in the compiled kernels. -/
inductive DpasShape where
  | m8n8
  | m8n16
  deriving Repr, DecidableEq

def DpasShape.m : DpasShape → Nat
  | .m8n8 | .m8n16 => 8

def DpasShape.n : DpasShape → Nat
  | .m8n8 => 8
  | .m8n16 => 16

/-- The ISA depth of one atom for a source type. -/
def DpasType.k : DpasType → Nat
  | .hf8 => 32
  | .f16 | .bf16 => 16
  | .f32 => 8

/-- A decoded DPAS instruction. -/
structure DpasForm where
  shape : DpasShape
  exec : Nat
  src : DpasType
  acc : DpasType
  deriving Repr, DecidableEq

def parseDpasShape (s : String) : Option DpasShape :=
  if s = "dpas.8x8" then some .m8n8
  else if s = "dpas.8x16" then some .m8n16
  else none

/-- `(16|M0)` -> 16. -/
def parseDpasExec (s : String) : Option Nat :=
  match numRuns s with
  | n :: _ => some n
  | [] => none

def parseDpasType (s : String) : Option DpasType :=
  match afterColon s.toList with
  | some ['f'] => some .f32
  | some ['h', 'f', '8'] => some .hf8
  | some ['f', '1', '6'] => some .f16
  | some ['b', 'f', '1', '6'] => some .bf16
  | _ => none

/-- Decode a DPAS line: mnemonic, execution size, accumulator destination and
the two source operands. -/
def parseDpas (mnemonic exec dst src1 src2 : String) : Option DpasForm :=
  match parseDpasShape mnemonic, parseDpasExec exec, parseDpasType dst,
      parseDpasType src1, parseDpasType src2 with
  | some sh, some n, some acc, some a, some b =>
      if a = b then some ⟨sh, n, a, acc⟩ else none
  | _, _, _, _, _ => none

/-- The first DPAS of the compiled FMHA mainloop, decoded. -/
theorem realFmhaDpas_form :
    parseDpas "dpas.8x8" "(16|M0)" "r383:f" "r39:hf8" "r335.0:hf8" =
      some ⟨.m8n8, 16, .hf8, .f32⟩ := by
  decide

/-- The compiled FMHA atom is 8x8, not the model's 8x16. -/
theorem fmhaDpas_not_tlaAtom :
    DpasShape.m8n8 ≠ DpasShape.m8n16 := by
  decide

/-- Its fp8 depth is 32: one 8x8x32 atom, not the 16+16 split. -/
theorem fmhaDpas_depth : DpasType.hf8.k = 32 := rfl

/-- The existing `dpasSlab_two_atoms` depth and the FMHA depth agree, but the
shapes differ; the two-atom decomposition is scoped to the 8x16x16 atom. -/
theorem fmhaDpas_shape_and_depth :
    DpasShape.m8n8.m = 8 ∧ DpasShape.m8n8.n = 8 ∧ DpasType.hf8.k = 32 :=
  ⟨rfl, rfl, rfl⟩


/-- A DPAS atom shape: M, N, K depth, source and accumulator types. -/
structure DpasAtomShape where
  m : Nat
  n : Nat
  k : Nat
  src : DpasType
  acc : DpasType
  deriving Repr, DecidableEq

/-- The SYCL-TLA `XE_8x16x16_F32F16F16F32` atom. -/
def tlaXeF16Atom : DpasAtomShape := ⟨8, 16, 16, .f16, .f32⟩

/-- The compiled FMHA fp8 atom: one 8x8x32 DPAS. -/
def fmhaFp8Atom : DpasAtomShape := ⟨8, 8, 32, .hf8, .f32⟩

/-- The decoded form's atom shape. -/
def DpasForm.toAtom (f : DpasForm) : DpasAtomShape :=
  ⟨f.shape.m, f.shape.n, f.src.k, f.src, f.acc⟩

/-- The decoded FMHA instruction is exactly the 8x8x32 fp8 atom. -/
theorem realFmhaDpas_atom :
    (parseDpas "dpas.8x8" "(16|M0)" "r383:f" "r39:hf8" "r335.0:hf8").map DpasForm.toAtom =
      some fmhaFp8Atom := by
  decide

/-- DPAS instructions per K=32 tile for an atom of depth `atomK`. -/
def atomsPerTile (atomK kTile : Nat) : Nat := kTile / atomK

/-- One K=32 tile needs one FMHA fp8 DPAS. -/
theorem fmha_fp8_k32_atoms : atomsPerTile fmhaFp8Atom.k 32 = 1 := by
  decide

/-- The same K=32 tile needs two SYCL-TLA fp16 DPAS instructions. -/
theorem tla_f16_k32_atoms : atomsPerTile tlaXeF16Atom.k 32 = 2 := by
  decide

/-- The N dims differ: 8 for FMHA fp8, 16 for SYCL-TLA fp16. -/
theorem fmha_atom_not_tla : fmhaFp8Atom.n ≠ tlaXeF16Atom.n := by
  decide

end IntelGpu
