-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaBlockCensus
public import Intel.TlaDpasSum

@[expose] public section

/-!
# The DPAS phase of the SYCL-TLA mainloop

The mainloop block `[959, 1404)` contains the 32 DPAS instructions of the
kernel. This module extracts that subsequence with its program counters,
proves it is exactly `realTlaGemmDpas`, and instantiates the 32-step slab sum
on the mainloop phase.

`mainloopDpasRun` is the register-file effect of the mainloop's DPAS phase. It
is the loop-carried accumulator update that the remaining mainloop
instructions (tile loads, syncs and the back-edge) have to preserve.
-/

namespace IntelGpu

/-- The DPAS instructions in the mainloop block, with their program counters. -/
def blockDpasPc : List (Nat × TlaDpas) :=
  blockInstrs.filterMap (fun p => (parseTlaDpas p.2).map (fun d => (p.1, d)))

/-- The DPAS phase of the mainloop, in program order. -/
def blockDpasSeq : List TlaDpas := blockDpasPc.map (fun p => p.2)

set_option maxRecDepth 100000 in
/-- The mainloop block contains 32 DPAS instructions. -/
theorem blockDpasPc_length : blockDpasPc.length = 32 := by decide

set_option maxRecDepth 100000 in
/-- The block's DPAS program counters are exactly `dpasPcs`. -/
theorem blockDpasPc_pcs : blockDpasPc.map (fun p => p.1) = dpasPcs := by decide

set_option maxRecDepth 100000 in
/-- The block's DPAS sequence is the decoded program's DPAS sequence. -/
theorem blockDpasSeq_eq : blockDpasSeq = realTlaGemmDpas := by decide

/-- The register-file effect of the mainloop's DPAS phase. -/
def mainloopDpasRun (rf : RegFile) : RegFile := tlaDpasRunSeq blockDpasSeq rf

theorem mainloopDpasRun_eq (rf : RegFile) :
    mainloopDpasRun rf = tlaDpasRun realTlaGemmDpas rf := by
  simp [mainloopDpasRun, blockDpasSeq_eq, tlaDpasRunSeq_eq]

/-- The mainloop DPAS phase accumulates the ordered slab sum into `r21..r28`. -/
theorem mainloopDpasRun_acc0_sum (rf : RegFile) (m n : Nat) (hm : m < 8) (hn : n < 8) :
    readTileC (mainloopDpasRun rf) 21 m n =
      readTileC rf 21 m n +
        (realTlaGemmDpas.map (fun d =>
          dpasSlab 16 (readTileA rf d.srcA) (readTileB rf d.srcB 0) m n)).sum := by
  simp only [mainloopDpasRun, blockDpasSeq_eq]
  rw [tlaDpasRunSeq_eq]
  exact realTlaGemmDpas_acc0_sum rf m n hm hn

/-- The mainloop DPAS phase accumulates the ordered slab sum into `r13..r20`. -/
theorem mainloopDpasRun_acc1_sum (rf : RegFile) (m n : Nat) (hm : m < 8) (hn : n < 8) :
    readTileC (mainloopDpasRun rf) 13 m n =
      readTileC rf 13 m n +
        (realTlaGemmDpas.map (fun d =>
          dpasSlab 16 (readTileA rf d.srcA) (readTileB rf d.srcB 0) m n)).sum := by
  simp only [mainloopDpasRun, blockDpasSeq_eq]
  rw [tlaDpasRunSeq_eq]
  exact realTlaGemmDpas_acc1_sum rf m n hm hn

end IntelGpu
