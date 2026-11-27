-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaDecode
public import Intel.FmhaExec

@[expose] public section

/-!
# Register-level execution of the SYCL-TLA GEMM DPAS chain

`Intel.TlaDecode` total-decodes the real SYCL-TLA GEMM dump into labels,
predicated forms, DPAS and plain instructions. This module executes the DPAS
subset on the logical register file of `Intel.FmhaExec`.

The kernel uses `dpas.8x8 (16|M0)` with two FP32 accumulator bases and two BF16
source bases. The 32 instructions all accumulate into the same two blocks,
`r21` and `r13`, while sweeping the B base over `64..120` and the A base over
`30..58`. We model one instruction as an 8x8 depth-16 slab applied to each
accumulator block, and prove that the 32-step fold accumulates the sum of the
slabs into both blocks and frames everything else.

The numerical interpretation of the BF16 source bits is not part of this
stage: the slab is the same algebraic `Word` model used by the existing DPAS
development. Connecting the decoded BF16 bits to that model is a later stage.
-/

namespace IntelGpu

/-- The register bases of one decoded SYCL-TLA DPAS. -/
structure TlaDpas where
  acc0 : Nat
  acc1 : Nat
  srcB : Nat
  srcA : Nat
  deriving Repr, DecidableEq

/-- Parse one decoded DPAS into its four register bases. -/
def parseTlaDpas : TlaInstr → Option TlaDpas
  | .dpas _ d0 d1 b a _ =>
      match parseDpasReg d0, parseDpasReg d1, parseDpasReg b, parseDpasReg a with
      | some (r0, _), some (r1, _), some (rb, _), some (ra, _) =>
          some ⟨r0, r1, rb, ra⟩
      | _, _, _, _ => none
  | _ => none

/-- The 32 DPAS instructions of the real SYCL-TLA GEMM. -/
def realTlaGemmDpas : List TlaDpas :=
  (decodeTlaProgram realTlaGemm).filterMap parseTlaDpas

/-- One depth-16 atom applied to an accumulator block. -/
def tlaSlab (A B C : Nat → Nat → Word) (m n : Nat) : Word :=
  C m n + dpasSlab 16 A B m n

/-- Execute one DPAS on a register file. The A/B tiles are read before either
accumulator is written. -/
def tlaDpasStep (rf : RegFile) (acc0 acc1 srcB srcA : Nat) : RegFile :=
  let A := readTileA rf srcA
  let B := readTileB rf srcB 0
  let C0 := readTileC rf acc0
  let C1 := readTileC rf acc1
  writeTileC (writeTileC rf acc0 (tlaSlab A B C0)) acc1 (tlaSlab A B C1)

/-- Execute one decoded DPAS. -/
def tlaDpasStepOf (d : TlaDpas) (rf : RegFile) : RegFile :=
  tlaDpasStep rf d.acc0 d.acc1 d.srcB d.srcA

/-- Execute a list of DPAS instructions in order. -/
def tlaDpasRun (steps : List TlaDpas) (rf : RegFile) : RegFile :=
  steps.foldl (fun rf d => tlaDpasStepOf d rf) rf

/-- The first accumulator block after one step. -/
theorem tlaDpasStep_acc0 (rf : RegFile) (acc0 acc1 srcB srcA : Nat)
    (hdisj : TileCDisjoint acc0 acc1) (m n : Nat) (hm : m < 8) (hn : n < 8) :
    readTileC (tlaDpasStep rf acc0 acc1 srcB srcA) acc0 m n =
      tlaSlab (readTileA rf srcA) (readTileB rf srcB 0) (readTileC rf acc0) m n := by
  unfold tlaDpasStep
  rw [readTileC_writeTileC_of_disjoint _ _ _ _ hdisj m n hm hn]
  exact readTileC_writeTileC _ _ _ m n hm hn

/-- The second accumulator block after one step. -/
theorem tlaDpasStep_acc1 (rf : RegFile) (acc0 acc1 srcB srcA : Nat)
    (m n : Nat) (hm : m < 8) (hn : n < 8) :
    readTileC (tlaDpasStep rf acc0 acc1 srcB srcA) acc1 m n =
      tlaSlab (readTileA rf srcA) (readTileB rf srcB 0) (readTileC rf acc1) m n := by
  unfold tlaDpasStep
  exact readTileC_writeTileC _ _ _ m n hm hn

/-- Everything outside both accumulator blocks is unchanged. -/
theorem tlaDpasStep_frame (rf : RegFile) (acc0 acc1 srcB srcA r e : Nat)
    (h0 : ¬ inTileC acc0 r e) (h1 : ¬ inTileC acc1 r e) :
    tlaDpasStep rf acc0 acc1 srcB srcA r e = rf r e := by
  unfold tlaDpasStep
  rw [writeTileC_frame _ _ _ _ _ h1, writeTileC_frame _ _ _ _ _ h0]

set_option maxRecDepth 100000 in
/-- The real kernel has 32 decoded DPAS instructions. -/
theorem realTlaGemmDpas_length : realTlaGemmDpas.length = 32 := by decide

set_option maxRecDepth 100000 in
/-- Every DPAS accumulates into `r21` and `r13`. -/
theorem realTlaGemmDpas_accs :
    realTlaGemmDpas.all (fun d => d.acc0 = 21 && d.acc1 = 13) = true := by decide

set_option maxRecDepth 100000 in
/-- Every B base is one of `64, 72, ..., 120`. -/
theorem realTlaGemmDpas_srcB_subset :
    realTlaGemmDpas.all (fun d =>
      d.srcB ∈ [64, 72, 80, 88, 96, 104, 112, 120]) = true := by
  decide

set_option maxRecDepth 100000 in
/-- Every base in `64, 72, ..., 120` occurs as a B base. -/
theorem realTlaGemmDpas_srcB_cover :
    ([64, 72, 80, 88, 96, 104, 112, 120].all (fun b =>
      realTlaGemmDpas.any (fun d => d.srcB = b))) = true := by
  decide

set_option maxRecDepth 100000 in
/-- Every A base is one of `30, 34, ..., 58`. -/
theorem realTlaGemmDpas_srcA_subset :
    realTlaGemmDpas.all (fun d =>
      d.srcA ∈ [30, 34, 38, 42, 46, 50, 54, 58]) = true := by
  decide

set_option maxRecDepth 100000 in
/-- Every base in `30, 34, ..., 58` occurs as an A base. -/
theorem realTlaGemmDpas_srcA_cover :
    ([30, 34, 38, 42, 46, 50, 54, 58].all (fun a =>
      realTlaGemmDpas.any (fun d => d.srcA = a))) = true := by
  decide

set_option maxRecDepth 100000 in
/-- The first decoded DPAS is the expected `r21/r13/r64/r30` form. -/
theorem realTlaGemmDpas_first :
    realTlaGemmDpas.head? = some ⟨21, 13, 64, 30⟩ := by
  decide

end IntelGpu
