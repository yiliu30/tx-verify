-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.Examples.RealTlaGemm
public import Intel.RealDpas
public import Intel.RealDecode

@[expose] public section

/-!
# Coverage of the real SYCL-TLA GEMM dump

`Intel.Examples.RealTlaGemm` is the raw IGC assembly of the SYCL-TLA
GEMM example (256x256x32, BF16 inputs, FP32 accumulator). This module
records what the current decoder does with it and censuses its DPAS
instructions.

The decoder rejects the program at the first instruction: the dump uses the
predicated `(W) mov` spelling for its per-thread prologue, while `decodeReal`
only accepts the forms transcribed for the smaller kernels. The 32 DPAS
instructions use `dpas.8x8 (16|M0)` with two FP32 accumulator bases and two
BF16 source bases, i.e. the SYCL-TLA 8x16x16 atom implemented as a pair of 8x8
results. The census proves the shape, execution size, operand types and the
two 8-element source-base lattices.
-/

namespace IntelGpu

/-- A `dpas.8x8` statement. -/
def isTlaDpas : Stmt → Bool
  | .instruction "dpas.8x8" _ => true
  | _ => false

/-- The DPAS statements of the real GEMM. -/
def tlaGemmDpasStmts : List Stmt := realTlaGemm.statements.filter isTlaDpas

/-- The DPAS form used by this kernel: 8x8, 16 lanes, two FP32 accumulators and
two BF16 sources. -/
def isBf16Dpas : Stmt → Bool
  | .instruction "dpas.8x8" [e, d0, d1, b, a, _] =>
      (parseDpasExec e == some 16) &&
      (afterColon d0.toList == some ['f']) &&
      (afterColon d1.toList == some ['f']) &&
      (afterColon b.toList == some ['b', 'f']) &&
      (afterColon a.toList == some ['b', 'f'])
  | _ => false

/-- The B source base of a DPAS statement. -/
def dpasSrcB : Stmt → Option Nat
  | .instruction "dpas.8x8" [_, _, _, b, _, _] => (numRuns (operandCore b)).head?
  | _ => none

/-- The A source base of a DPAS statement. -/
def dpasSrcA : Stmt → Option Nat
  | .instruction "dpas.8x8" [_, _, _, _, a, _] => (numRuns (operandCore a)).head?
  | _ => none

/-- The B base is in the given lattice. -/
def inBasesB (bases : List Nat) (s : Stmt) : Bool :=
  match dpasSrcB s with
  | some b => bases.elem b
  | none => false

/-- The A base is in the given lattice. -/
def inBasesA (bases : List Nat) (s : Stmt) : Bool :=
  match dpasSrcA s with
  | some a => bases.elem a
  | none => false

set_option maxRecDepth 100000 in
/-- The raw import has 2252 statements. -/
theorem realTlaGemm_stmt_count : realTlaGemm.statements.length = 2252 := by decide

set_option maxRecDepth 100000 in
/-- The kernel contains 32 DPAS statements. -/
theorem realTlaGemm_dpas_count : tlaGemmDpasStmts.length = 32 := by decide

set_option maxRecDepth 100000 in
/-- Every DPAS is 8x8 with 16 lanes, two FP32 accumulators and two BF16 sources. -/
theorem realTlaGemm_dpas_all_bf16 : tlaGemmDpasStmts.all isBf16Dpas = true := by
  decide

set_option maxRecDepth 100000 in
/-- Every B source base lies in `64, 72, ..., 120`. -/
theorem realTlaGemm_srcB_bases_subset :
    tlaGemmDpasStmts.all (inBasesB [64, 72, 80, 88, 96, 104, 112, 120]) = true := by
  decide

set_option maxRecDepth 100000 in
/-- Every base in `64, 72, ..., 120` occurs as a B source. -/
theorem realTlaGemm_srcB_bases_cover :
    ([64, 72, 80, 88, 96, 104, 112, 120].all (fun b =>
      tlaGemmDpasStmts.any (fun s => dpasSrcB s == some b))) = true := by
  decide

set_option maxRecDepth 100000 in
/-- Every A source base lies in `30, 34, ..., 58`. -/
theorem realTlaGemm_srcA_bases_subset :
    tlaGemmDpasStmts.all (inBasesA [30, 34, 38, 42, 46, 50, 54, 58]) = true := by
  decide

set_option maxRecDepth 100000 in
/-- Every base in `30, 34, ..., 58` occurs as an A source. -/
theorem realTlaGemm_srcA_bases_cover :
    ([30, 34, 38, 42, 46, 50, 54, 58].all (fun a =>
      tlaGemmDpasStmts.any (fun s => dpasSrcA s == some a))) = true := by
  decide

/-- The first instruction after the entry label is the predicated prologue. -/
theorem realTlaGemm_first_instruction :
    realTlaGemm.statements[1]? =
      some (.instruction "(W) mov" ["(16|M0)", "r127.0<1>:ud", "0x0:ud"]) := by
  rfl

/-- That prologue form is not in the decoder. -/
theorem realTlaGemm_first_rejected :
    decodeReal (.instruction "(W) mov" ["(16|M0)", "r127.0<1>:ud", "0x0:ud"]) = none := by
  decide

set_option maxRecDepth 100000 in
/-- The current decoder rejects the whole SYCL-TLA GEMM program. -/
theorem realTlaGemm_rejected : decodeRealProgram realTlaGemm = none := by decide

end IntelGpu
