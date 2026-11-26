#!/usr/bin/env python3
"""Audit the axiom footprint of every headline theorem.

Each entry is (module, theorem). The script writes a temporary Lean file that
prints the axioms of each theorem, runs it, and fails if any theorem depends on
anything outside the allowed set.

Run from the repository root, on a machine with Lean installed:

    python3 Tools/check_axioms.py

Extra names may be appended with ``--also Module.theorem``.
"""
from __future__ import annotations

import argparse
import pathlib
import re
import subprocess
import sys
import tempfile

ALLOWED = {"propext", "Quot.sound"}

# Theorems whose extra axioms are known and explained. `String.toList` in the
# core library is itself proved with `Classical.choice`, so anything that walks
# a `String` inherits it. The stage-5 decoder walks strings; it reasons about
# data only, so the dependency is benign but visible.
KNOWN = {
    "IntelGpu.decode_gemmLoop": {"Classical.choice"},
    # These go through `decodeInstr`, hence through `String.toList`.
    "IntelGpu.realAddOne_rejected": {"Classical.choice"},
    "IntelGpu.realAddOne_unsupported": {"Classical.choice"},
    # Stage 63 decoder: same `String.toList` path, plus `decide`-evaluated
    # operand parsing. The theorems talk about parsed data only.
    "IntelGpu.realAddOne_decodes": {"Classical.choice"},
    "IntelGpu.realAddOne_decoded_length": {"Classical.choice"},
    "IntelGpu.realAddOne_load": {"Classical.choice"},
    "IntelGpu.realAddOne_addImm": {"Classical.choice"},
    "IntelGpu.realAddOne_store": {"Classical.choice"},
    "IntelGpu.parseExec_rejects_extra_field": {"Classical.choice"},
    "IntelGpu.decodeReal_rejects_truncated": {"Classical.choice"},
    "IntelGpu.decodeReal_rejects_region_payload": {"Classical.choice"},
    # Stage 64 store model: `storeVec` picks a lane with `Classical.choose`
    # when addresses alias, and `stepReal` embeds that choice.
    "IntelGpu.storeVec_same": {"Classical.choice"},
    "IntelGpu.storeVec_frame": {"Classical.choice"},
    "IntelGpu.runReal_append": {"Classical.choice"},
    "IntelGpu.realAddOne_preamble_mem": {"Classical.choice"},
    "IntelGpu.realAddOne_tail_mem": {"Classical.choice"},
    "IntelGpu.realAddOne_mem": {"Classical.choice"},
    "IntelGpu.realAddOne_halted": {"Classical.choice"},
    "IntelGpu.realAddOne_effect": {"Classical.choice"},
    # The address proof and the decode bridge inherit the same model.
    "IntelGpu.realAddOne_address_preamble": {"Classical.choice"},
    "IntelGpu.realAddOne_decoded_eq": {"Classical.choice"},
    # Stage 65 GEMM coverage: `decodeReal` walks `String` operands.
    "IntelGpu.realGemm_accepted": {"Classical.choice"},
    "IntelGpu.realGemm_rejectedOps": {"Classical.choice"},
    "IntelGpu.realGemm_rejectedLabels": {"Classical.choice"},
    "IntelGpu.realGemm_decodes": {"Classical.choice"},
    "IntelGpu.realGemm_decoded_length": {"Classical.choice"},
    "IntelGpu.realGemm_label_main": {"Classical.choice"},
    "IntelGpu.realGemm_label_loop": {"Classical.choice"},
    "IntelGpu.realGemm_label_step": {"Classical.choice"},
    "IntelGpu.realGemm_label_exit": {"Classical.choice"},
    # Stage 67 byte refinement: composed with the stage-64 store model.
    "IntelGpu.realAddOne_byte_word_increment": {"Classical.choice"},
    # Stage 68 GEMM preamble: `decodeRealProgram` walks strings, and
    # `stepWith` embeds the store model's `Classical.choose`.
    "IntelGpu.realGemm_preamble_prefix": {"Classical.choice"},
    "IntelGpu.gemmPreamble_i": {"Classical.choice"},
    "IntelGpu.gemmPreamble_j": {"Classical.choice"},
    "IntelGpu.gemmPreamble_shift": {"Classical.choice"},
    "IntelGpu.gemmPreamble_counter": {"Classical.choice"},
    "IntelGpu.gemmPreamble_sum": {"Classical.choice"},
    "IntelGpu.gemmPreamble_entry": {"Classical.choice"},
    # Stage 69 GEMM loop indices: `stepWith` embeds the store model's choice.
    "IntelGpu.gemmIndexA": {"Classical.choice"},
    "IntelGpu.gemmIndexB": {"Classical.choice"},
    # Stage 70 GEMM loop body: the same `stepWith`/store-model path.
    "IntelGpu.gemmAddressA": {"Classical.choice"},
    "IntelGpu.gemmAddressB": {"Classical.choice"},
    "IntelGpu.gemmLoadA": {"Classical.choice"},
    "IntelGpu.gemmLoadB": {"Classical.choice"},
    "IntelGpu.gemmProduct": {"Classical.choice"},
    "IntelGpu.gemmSum": {"Classical.choice"},
    "IntelGpu.gemmBody": {"Classical.choice"},
    # Stage 71 GEMM loop step: the same `stepWith`/store-model path.
    "IntelGpu.gemmBodyBlock_frame": {"Classical.choice"},
    "IntelGpu.gemmBodyStep_counter": {"Classical.choice"},
    "IntelGpu.gemmBodyStep_pred": {"Classical.choice"},
    "IntelGpu.gemmBodyStep_mem": {"Classical.choice"},
    "IntelGpu.gemmBodyStep_sum": {"Classical.choice"},
    "IntelGpu.gemmBodyStep_frame": {"Classical.choice"},
    "IntelGpu.gemmBodyStep_inv": {"Classical.choice"},
    "IntelGpu.gemmEpilogue_address": {"Classical.choice"},
    "IntelGpu.gemmStepIter_inv": {"Classical.choice"},
    "IntelGpu.gemmFinalStep_sum": {"Classical.choice"},
    "IntelGpu.gemmFinalStep_pred": {"Classical.choice"},
    "IntelGpu.gemmFinalStep_frame": {"Classical.choice"},
    "IntelGpu.gemmFinalStep_inv": {"Classical.choice"},
    "IntelGpu.gemmLoop_final": {"Classical.choice"},
    "IntelGpu.gemmEpilogue_mem": {"Classical.choice"},
    "IntelGpu.gemmEpilogue_store_at": {"Classical.choice"},
    "IntelGpu.gemmEpilogue_store_mem": {"Classical.choice"},
    "IntelGpu.gemmEpilogue_halted": {"Classical.choice"},
    "IntelGpu.realGemm_output": {"Classical.choice"},
    "IntelGpu.realFmhaDpas_form": {"Classical.choice"},
    "IntelGpu.realFmhaDpas_atom": {"Classical.choice"},
    "IntelGpu.realFmhaDpas_regs": {"Classical.choice"},
    # Stage 82 vector-add coverage: `decodeReal` walks `String` operands.
    "IntelGpu.realVectorAdd_accepted": {"Classical.choice"},
    "IntelGpu.realVectorAdd_rejectedOps": {"Classical.choice"},
    "IntelGpu.realVectorAdd_rejectedLabels": {"Classical.choice"},
    "IntelGpu.masked_mov_decodes": {"Classical.choice"},
    "IntelGpu.masked_stride2_decodes": {"Classical.choice"},
    "IntelGpu.realVectorAdd_preamble_prefix": {"Classical.choice"},
    "IntelGpu.vaLoopPreamble_id": {"Classical.choice"},
    "IntelGpu.vaLoopPreamble_mem": {"Classical.choice"},
    "IntelGpu.setQword_low": {"Classical.choice"},
    "IntelGpu.realVectorAdd_body_prefix": {"Classical.choice"},
    "IntelGpu.vaLoopBody_mem": {"Classical.choice"},
    "IntelGpu.vaLoopBody_sum": {"Classical.choice"},
    "IntelGpu.vaLoopBody_store_at": {"Classical.choice"},
    "IntelGpu.vaLoopPreamble_frame": {"Classical.choice"},
    "IntelGpu.vaLoopPreamble_bodyPre": {"Classical.choice"},
    "IntelGpu.realVectorAdd_loop_effect": {"Classical.choice"},
    "IntelGpu.vaLoopPreamble_size": {"Classical.choice"},
    "IntelGpu.realVectorAdd_decoded_eq": {"Classical.choice"},
    "IntelGpu.vaLoop_first_exit": {"Classical.choice"},
    "IntelGpu.vaLoop_first_body": {"Classical.choice"},
    "IntelGpu.vaLoop_second_exit": {"Classical.choice"},
    "IntelGpu.vaLoop_second_select": {"Classical.choice"},
    "IntelGpu.vaLoopP3": {"Classical.choice"},
    "IntelGpu.vaLoopP6": {"Classical.choice"},
    "IntelGpu.stepLoop_mov61_unit": {"Classical.choice"},
    "IntelGpu.stepLoop_mov74_unit": {"Classical.choice"},
    "IntelGpu.stepLoop_movMasked61_unit": {"Classical.choice"},
    "IntelGpu.stepLoop_movMasked74_unit": {"Classical.choice"},
    "IntelGpu.parseExec_rejects_M9": {"Classical.choice"},
    "IntelGpu.predicated_gotos_decode": {"Classical.choice"},
    "IntelGpu.realVectorAdd_decodes": {"Classical.choice"},
    "IntelGpu.realVectorAdd_decoded_length": {"Classical.choice"},
    # Stage 83 vector-add decode/preamble: `String.toList` and `stepWith`.
    "IntelGpu.realVectorAddFlat_preamble_prefix": {"Classical.choice"},
    "IntelGpu.realVectorAddFlat_decodes": {"Classical.choice"},
    "IntelGpu.realVectorAddFlat_decoded_length": {"Classical.choice"},
    "IntelGpu.vaPreamble_id": {"Classical.choice"},
    "IntelGpu.cmpLt_lane": {"Classical.choice"},
    "IntelGpu.cmpLt_other": {"Classical.choice"},
    "IntelGpu.cmpLt_inactive": {"Classical.choice"},
    # Stage 91 predicated select: `stepWith` embeds the store model's choice.
    "IntelGpu.sel_lane": {"Classical.choice"},
    # Stage 96 masked move: `stepWith` embeds the store model's choice.
    "IntelGpu.maskedMov_unit_lane": {"Classical.choice"},
    "IntelGpu.maskedMov_stride2_lane": {"Classical.choice"},
    "IntelGpu.maskedMov_frame": {"Classical.choice"},
    "IntelGpu.maskedMov_other_reg": {"Classical.choice"},
    # Stage 100 address injectivity: `omega` over the div/mod constraints.
    "IntelGpu.fmhaAAddr_injective16": {"Classical.choice"},
    "IntelGpu.fmhaCAddr_injective16": {"Classical.choice"},
    # Stage 93 predicate logic: `stepWith` embeds the store model's choice.
    "IntelGpu.predAnd_lane": {"Classical.choice"},
    "IntelGpu.predAnd_other": {"Classical.choice"},
    "IntelGpu.predAnd_inactive": {"Classical.choice"},
    "IntelGpu.predOr_lane": {"Classical.choice"},
    "IntelGpu.predOr_other": {"Classical.choice"},
    "IntelGpu.predOr_inactive": {"Classical.choice"},
    # Stage 94 register comparisons: `stepWith` embeds the store model's choice.
    "IntelGpu.cmpLtReg_lane": {"Classical.choice"},
    "IntelGpu.cmpLtReg_other": {"Classical.choice"},
    "IntelGpu.cmpLtReg_inactive": {"Classical.choice"},
    "IntelGpu.cmpEqReg_lane": {"Classical.choice"},
    "IntelGpu.cmpEqReg_other": {"Classical.choice"},
    "IntelGpu.cmpEqReg_inactive": {"Classical.choice"},
    "IntelGpu.vaPreamble_pointers": {"Classical.choice"},
    "IntelGpu.vaPreamble_mem": {"Classical.choice"},
    "IntelGpu.realVectorAddFlat_decoded_eq": {"Classical.choice"},
    "IntelGpu.vaLoadA": {"Classical.choice"},
    "IntelGpu.vaLoadB": {"Classical.choice"},
    "IntelGpu.vaAdd": {"Classical.choice"},
    "IntelGpu.vaTail_halted": {"Classical.choice"},
    "IntelGpu.vaMem": {"Classical.choice"},
    "IntelGpu.vaStore": {"Classical.choice"},
    "IntelGpu.vaRun_append": {"Classical.choice"},
    "IntelGpu.vaFrame": {"Classical.choice"},
    "IntelGpu.realVectorAdd_effect": {"Classical.choice"},
}

# One headline theorem per stage, in stage order.
THEOREMS = [
    ("Intel.AddOne", "IntelGpu.core_correct"),
    ("Intel.Gemm", "IntelGpu.gemmRun_acc"),
    ("Intel.GemmBody", "IntelGpu.gemmBody_correct"),
    ("Intel.Examples.GemmLoopDecoded", "IntelGpu.decode_gemmLoop"),
    ("Intel.GemmControl", "IntelGpu.gemmBodyD_correct"),
    ("Intel.GemmLoop", "IntelGpu.dotProgram_correct"),
    ("Intel.Address", "IntelGpu.gemmMemoryBody_correct"),
    ("Intel.GemmMemoryLoop", "IntelGpu.mProgram_correct"),
    ("Intel.GemmMatrix", "IntelGpu.mProgram_matrix"),
    ("Intel.GemmTiling", "IntelGpu.gemmSpecW_of_tiles"),
    ("Intel.GemmScheduler", "IntelGpu.mem_tileSchedule_of_lt"),
    ("Intel.GemmScheduleProof", "IntelGpu.gemmSpecW_of_schedule"),
    ("Intel.GemmSlm", "IntelGpu.gemmTile_slm_correct"),
    ("Intel.SlmLatency", "IntelGpu.fresh_with_barrier"),
    ("Intel.Divergence", "IntelGpu.barrier_needs_all_lanes"),
    ("Intel.Simd", "IntelGpu.add_one_simd"),
    ("Intel.MemoryLaws", "IntelGpu.store32_store32_commute"),
    ("Intel.RealCoverage", "IntelGpu.realAddOne_unsupported"),
    ("Intel.GemmSlmCompute", "IntelGpu.gemmTile_executed"),
    ("Intel.Dpas", "IntelGpu.dpasRun_correct"),
    ("Intel.GemmDpasLoop", "IntelGpu.dpasProg_correct"),
    ("Intel.TlaInstance", "IntelGpu.tlaXeF16_gemm_spec"),
    ("Intel.DpasAtom", "IntelGpu.dpasSlab_two_atoms"),
    ("Intel.DpasMask", "IntelGpu.tlaXeF16_gemm_spec_tail"),
    ("Intel.Epilogue", "IntelGpu.gemmTile_end_to_end"),
    ("Intel.EpilogueLd", "IntelGpu.epilogueLd_correct"),
    ("Intel.EpilogueFrame", "IntelGpu.epilogueLd_frame"),
    ("Intel.SharedBuffer", "IntelGpu.writeTiles_frame"),
    ("Intel.SharedBuffer", "IntelGpu.separated_of_width"),
    ("Intel.SharedBuffer", "IntelGpu.writeTiles_block"),
    ("Intel.GemmAssembly", "IntelGpu.tlaXeF16_gemm_executed"),
    ("Intel.Staging", "IntelGpu.stageSlab_correct"),
    ("Intel.Mainloop", "IntelGpu.mainloop_correct"),
    ("Intel.LaneStaging", "IntelGpu.laneBlock_value"),
    ("Intel.Interleaved", "IntelGpu.copyInterleaved_value"),
    ("Intel.InterleavedLanes", "IntelGpu.lane_mod"),
    ("Intel.InterleavedLanes", "IntelGpu.lanesInterleaved_covers"),
    ("Intel.TilePipeline", "IntelGpu.mainloop_epilogue"),
    ("Intel.Numeric", "IntelGpu.maccDot_error"),
    ("Intel.Rounding", "IntelGpu.truncDot_error"),
    ("Intel.RoundingNearest", "IntelGpu.roundDot_error"),
    ("Intel.RoundingEven", "IntelGpu.evenDot_error"),
    ("Intel.NumericBridge", "IntelGpu.wpDot_error"),
    ("Intel.Exactness", "IntelGpu.evenDot_exact_on_grid"),
    ("Intel.Fp16Shape", "IntelGpu.fp16_grid_exact_of_exp"),
    ("Intel.Fp16Bits", "IntelGpu.fp16_bits_exact"),
    ("Intel.Fp16Value", "IntelGpu.foldVal_fin"),
    ("Intel.Fp16Value", "IntelGpu.vstep_nan_left"),
    ("Intel.Fp16Scaled", "IntelGpu.scaled_normal"),
    ("Intel.Fp16Gluing", "IntelGpu.scaled_eq_mag"),
    ("Intel.RealDecode", "IntelGpu.realAddOne_decodes"),
    ("Intel.RealDecode", "IntelGpu.realAddOne_load"),
    ("Intel.RealDecode", "IntelGpu.realAddOne_store"),
    ("Intel.RealSemantics", "IntelGpu.realAddOne_decoded_eq"),
    ("Intel.RealSemantics", "IntelGpu.realAddOne_address_preamble"),
    ("Intel.RealSemantics", "IntelGpu.realAddOne_effect"),
    ("Intel.RealGemmCoverage", "IntelGpu.realGemm_accepted"),
    ("Intel.RealGemmCoverage", "IntelGpu.realGemm_decodes"),
    ("Intel.RealGemmCoverage", "IntelGpu.realGemm_decoded_length"),
    ("Intel.RealGemmCoverage", "IntelGpu.realGemm_label_loop"),
    ("Intel.ByteMemory", "IntelGpu.wordView_store32LE"),
    ("Intel.ByteMemory", "IntelGpu.realAddOne_byteRangesDisjoint"),
    ("Intel.ByteMemory", "IntelGpu.realAddOne_byte_word_increment"),
    ("Intel.GemmReal", "IntelGpu.realGemm_preamble_prefix"),
    ("Intel.GemmReal", "IntelGpu.gemmPreamble_dst_counts"),
    ("Intel.GemmReal", "IntelGpu.gemmPreamble_entry"),
    ("Intel.GemmReal", "IntelGpu.gemmIndexA"),
    ("Intel.GemmReal", "IntelGpu.gemmIndexB"),
    ("Intel.GemmReal", "IntelGpu.gemmAddressA"),
    ("Intel.GemmReal", "IntelGpu.gemmAddressB"),
    ("Intel.GemmReal", "IntelGpu.gemmLoadA"),
    ("Intel.GemmReal", "IntelGpu.gemmLoadB"),
    ("Intel.GemmReal", "IntelGpu.gemmBody"),
    ("Intel.GemmReal", "IntelGpu.gemmBodyStep_sum"),
    ("Intel.GemmReal", "IntelGpu.gemmBodyStep_inv"),
    ("Intel.GemmReal", "IntelGpu.gemmEpilogue_address"),
    ("Intel.GemmRealLoop", "IntelGpu.gemmStepIter_inv"),
    ("Intel.GemmRealLoop", "IntelGpu.gemmFinalStep_inv"),
    ("Intel.GemmRealLoop", "IntelGpu.gemmDot_append"),
    ("Intel.GemmRealLoop", "IntelGpu.gemmLoop_final"),
    ("Intel.RealSemantics", "IntelGpu.predAnd_lane"),
    ("Intel.RealSemantics", "IntelGpu.predAnd_other"),
    ("Intel.RealSemantics", "IntelGpu.predAnd_inactive"),
    ("Intel.RealSemantics", "IntelGpu.predOr_lane"),
    ("Intel.RealSemantics", "IntelGpu.predOr_other"),
    ("Intel.RealSemantics", "IntelGpu.predOr_inactive"),
    ("Intel.RealSemantics", "IntelGpu.cmpLtReg_lane"),
    ("Intel.RealSemantics", "IntelGpu.cmpLtReg_other"),
    ("Intel.RealSemantics", "IntelGpu.cmpLtReg_inactive"),
    ("Intel.RealSemantics", "IntelGpu.cmpEqReg_lane"),
    ("Intel.RealSemantics", "IntelGpu.cmpEqReg_other"),
    ("Intel.RealSemantics", "IntelGpu.cmpEqReg_inactive"),
    ("Intel.RealSemantics", "IntelGpu.maskedMov_unit_lane"),
    ("Intel.RealSemantics", "IntelGpu.maskedMov_stride2_lane"),
    ("Intel.RealSemantics", "IntelGpu.maskedMov_frame"),
    ("Intel.RealSemantics", "IntelGpu.maskedMov_other_reg"),
    ("Intel.RealSemantics", "IntelGpu.writeMaskedWith_other_reg"),
    ("Intel.RealSemantics", "IntelGpu.runRealCFLaneWith_zero"),
    ("Intel.RealSemantics", "IntelGpu.runRealCFLane_gotoIf_taken"),
    ("Intel.RealSemantics", "IntelGpu.runRealCFLane_gotoIf_not_taken"),
    ("Intel.RealSemantics", "IntelGpu.mask_offset_load_bearing"),
    ("Intel.GemmRealLoop", "IntelGpu.gemmEpilogue_mem"),
    ("Intel.GemmRealLoop", "IntelGpu.gemmEpilogue_store"),
    ("Intel.GemmRealLoop", "IntelGpu.gemmEpilogue_store_mem"),
    ("Intel.GemmRealLoop", "IntelGpu.nat_wordC"),
    ("Intel.GemmRealLoop", "IntelGpu.realGemm_output"),
    ("Intel.SendSbid", "IntelGpu.wait_pending"),
    ("Intel.SendSbid", "IntelGpu.loadPipeline_value"),
    ("Intel.SendSbid", "IntelGpu.storePipeline_value"),
    ("Intel.SendSbid", "IntelGpu.addOnePipeline_value"),
    ("Intel.RealDpas", "IntelGpu.realFmhaDpas_form"),
    ("Intel.RealDpas", "IntelGpu.fmhaDpas_not_tlaAtom"),
    ("Intel.RealDpas", "IntelGpu.fmhaDpas_shape_and_depth"),
    ("Intel.RealDpas", "IntelGpu.realFmhaDpas_regs"),
    ("Intel.DpasPacking", "IntelGpu.fmhaPackedA_zero"),
    ("Intel.DpasPacking", "IntelGpu.fmhaPackedB_zero"),
    ("Intel.DpasPacking", "IntelGpu.fmhaPackedC_zero"),
    ("Intel.DpasPacking", "IntelGpu.fmhaRealPackedAtom_correct"),
    ("Intel.DpasPacking", "IntelGpu.fmhaRealB_address"),
    ("Intel.DpasPacking", "IntelGpu.fmhaBAddr_injective"),
    ("Intel.DpasPacking", "IntelGpu.fmhaAAddr_injective16"),
    ("Intel.DpasPacking", "IntelGpu.fmhaCAddr_injective16"),
    ("Intel.DpasPacking", "IntelGpu.fmhaReal_uses_decoded_bases"),
    ("Intel.DpasPacking", "IntelGpu.fmhaRealPackedAtom_ones"),
    ("Intel.DwordView", "IntelGpu.setDword_same"),
    ("Intel.DwordView", "IntelGpu.setDword_other"),
    ("Intel.DwordView", "IntelGpu.setQword_low"),
    ("Intel.DwordView", "IntelGpu.setQword_high"),
    ("Intel.DwordView", "IntelGpu.qwordOf_setQword"),
    ("Intel.DwordView", "IntelGpu.qwordOf_setDword_other"),
    ("Intel.VectorAddLoopBody", "IntelGpu.vaLoopWordNat"),
    ("Intel.VectorAddLoopBody", "IntelGpu.vaLoopWordNat4"),
    ("Intel.VectorAddLoopBody", "IntelGpu.vaLoopWordBitVec"),
    ("Intel.VectorAddLoopBody", "IntelGpu.realVectorAdd_body_prefix"),
    ("Intel.VectorAddLoopBody", "IntelGpu.vaLoopBody_mem"),
    ("Intel.VectorAddLoopBody", "IntelGpu.vaLoopBody_sum"),
    ("Intel.VectorAddLoopBody", "IntelGpu.vaLoopBody_store_at"),
    ("Intel.VectorAddLoopBody", "IntelGpu.vaLoopPreamble_frame"),
    ("Intel.VectorAddLoopBody", "IntelGpu.vaLoopPreamble_bodyPre"),
    ("Intel.VectorAddLoopBody", "IntelGpu.realVectorAdd_loop_effect"),
    ("Intel.VectorAddLoopBody", "IntelGpu.vaLoopNext_not_lt"),
    ("Intel.VectorAddLoop", "IntelGpu.vaLoopPreamble_size"),
    ("Intel.VectorAddLoopBody", "IntelGpu.vaLoopNext_guard_false"),
    ("Intel.VectorAddLoopProgram", "IntelGpu.realVectorAdd_decoded_eq"),
    ("Intel.VectorAddLoopProgram", "IntelGpu.vaLoopProgram_label_exit"),
    ("Intel.VectorAddLoopProgram", "IntelGpu.vaLoopProgram_label_loop"),
    ("Intel.VectorAddLoopProgram", "IntelGpu.vaLoopProgram_label_step"),
    ("Intel.VectorAddLoopProgram", "IntelGpu.vaLoopProgram_gotoIf_first"),
    ("Intel.VectorAddLoopProgram", "IntelGpu.vaLoopProgram_gotoIf_second"),
    ("Intel.VectorAddLoopProgram", "IntelGpu.vaLoop_first_exit"),
    ("Intel.VectorAddLoopProgram", "IntelGpu.vaLoop_first_body"),
    ("Intel.VectorAddLoopProgram", "IntelGpu.vaLoop_second_exit"),
    ("Intel.VectorAddLoopProgram", "IntelGpu.vaLoop_second_select"),
    ("Intel.LoopGuard", "IntelGpu.vaLoopP3"),
    ("Intel.LoopGuard", "IntelGpu.vaGuard32_eq"),
    ("Intel.LoopGuard", "IntelGpu.vaLoopP3_guard"),
    ("Intel.LoopGuard", "IntelGpu.vaLoopP6"),
    ("Intel.LoopGuard", "IntelGpu.vaLoopP6_guard"),
    ("Intel.LoopPack", "IntelGpu.packEven24_value"),
    ("Intel.LoopPack", "IntelGpu.packOdd24_value"),
    ("Intel.LoopPack", "IntelGpu.writeId24_qword"),
    ("Intel.LoopPack", "IntelGpu.selectId_true"),
    ("Intel.LoopPack", "IntelGpu.selectId_false"),
    ("Intel.LoopPack", "IntelGpu.writeId24_selected_qword"),
    ("Intel.LoopPack", "IntelGpu.packLow_dword"),
    ("Intel.LoopPack", "IntelGpu.packHigh_dword"),
    ("Intel.LoopPack", "IntelGpu.m5_m1_even"),
    ("Intel.LoopPack", "IntelGpu.m5_m1_odd"),
    ("Intel.LoopDwordStep", "IntelGpu.stepLoop_mov61_unit"),
    ("Intel.LoopDwordStep", "IntelGpu.stepLoop_mov74_unit"),
    ("Intel.LoopDwordStep", "IntelGpu.stepLoop_movMasked61_unit"),
    ("Intel.LoopDwordStep", "IntelGpu.stepLoop_movMasked74_unit"),
    ("Intel.Fp16Ieee", "IntelGpu.vstepIEEE_zero_left"),
    ("Intel.Fp16Ieee", "IntelGpu.foldValIEEE_fin"),
    ("Intel.Fp16Ieee", "IntelGpu.foldValIEEE_ne_fin"),
    ("Intel.Fp16Ieee", "IntelGpu.vstep_zero_inf_old"),
    ("Intel.RealVectorAddCoverage", "IntelGpu.realVectorAdd_accepted"),
    ("Intel.RealVectorAddCoverage", "IntelGpu.realVectorAdd_rejectedOps"),
    ("Intel.RealVectorAddCoverage", "IntelGpu.realVectorAdd_decodes"),
    ("Intel.RealVectorAddCoverage", "IntelGpu.realVectorAdd_decoded_length"),
    ("Intel.RealVectorAddCoverage", "IntelGpu.predicated_gotos_decode"),
    ("Intel.RealVectorAddCoverage", "IntelGpu.execMask_M5"),
    ("Intel.RealVectorAddCoverage", "IntelGpu.masked_mov_decodes"),
    ("Intel.RealVectorAddCoverage", "IntelGpu.masked_stride2_decodes"),
    ("Intel.VectorAddLoop", "IntelGpu.realVectorAdd_preamble_prefix"),
    ("Intel.VectorAddLoop", "IntelGpu.vaLoopPreamble_id"),
    ("Intel.VectorAddLoop", "IntelGpu.vaLoopPreamble_mem"),
    ("Intel.RealVectorAddCoverage", "IntelGpu.parseExec_rejects_M9"),
    ("Intel.VectorAdd", "IntelGpu.realVectorAddFlat_decoded_length"),
    ("Intel.VectorAdd", "IntelGpu.vaPreamble_id"),
    ("Intel.VectorAdd", "IntelGpu.vaLoadA"),
    ("Intel.VectorAdd", "IntelGpu.vaLoadB"),
    ("Intel.VectorAdd", "IntelGpu.vaAdd"),
    ("Intel.VectorAdd", "IntelGpu.vaTail_halted"),
    ("Intel.VectorAdd", "IntelGpu.vaMem"),
    ("Intel.VectorAdd", "IntelGpu.vaStore"),
    ("Intel.VectorAdd", "IntelGpu.vaFrame"),
    ("Intel.VectorAdd", "IntelGpu.realVectorAdd_effect"),
    ("Intel.VectorAdd", "IntelGpu.va_scale_load_bearing"),
]

LINE = re.compile(r"^'(?P<name>[^']+)' depends on axioms: \[(?P<axioms>[^\]]*)\]")


def discover() -> dict[str, list[str]]:
    """Every theorem in every Intel module, by module."""
    found: dict[str, list[str]] = {}
    for path in sorted(pathlib.Path("Intel").rglob("*.lean")):
        rel = path.relative_to("Intel").with_suffix("")
        module = "Intel." + ".".join(rel.parts)
        names = []
        for line in path.read_text().splitlines():
            if line.startswith("theorem "):
                names.append("IntelGpu." + line.split()[1])
        found[module] = names
    return found


def axioms_of_many(module: str, theorems: list[str]) -> dict[str, set[str]]:
    source = "\n".join(["import " + module, "", "open IntelGpu"]
                        + ["#print axioms " + t for t in theorems] + [""])
    with tempfile.TemporaryDirectory() as tmp:
        path = pathlib.Path(tmp) / "Audit.lean"
        path.write_text(source)
        proc = subprocess.run(["lake", "env", "lean", str(path)],
                              capture_output=True, text=True)
    out: dict[str, set[str]] = {}
    for line in (proc.stdout + proc.stderr).splitlines():
        match = LINE.match(line.strip())
        if match:
            out[match.group("name")] = {
                a.strip() for a in match.group("axioms").split(",") if a.strip()}
    return out


def axioms_of(module: str, theorem: str) -> set[str] | None:
    source = "\n".join(["import " + module, "", "open IntelGpu",
                         "#print axioms " + theorem, ""])
    with tempfile.TemporaryDirectory() as tmp:
        path = pathlib.Path(tmp) / "Audit.lean"
        path.write_text(source)
        proc = subprocess.run(["lake", "env", "lean", str(path)],
                              capture_output=True, text=True)
    for line in (proc.stdout + proc.stderr).splitlines():
        match = LINE.match(line.strip())
        if match and match.group("name") == theorem:
            return {a.strip() for a in match.group("axioms").split(",") if a.strip()}
    return None


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--also", action="append", default=[],
                        help="extra Module,theorem entries to audit")
    parser.add_argument("--all", action="store_true",
                        help="audit every theorem in every Intel module, not just the headlines")
    parser.add_argument("--md", action="store_true",
                        help="emit the curated stage table as Markdown")
    args = parser.parse_args()

    if args.all:
        modules = discover()
        bad: list[tuple[str, list[str]]] = []
        known: list[tuple[str, list[str]]] = []
        count = 0
        for module, theorems in modules.items():
            if not theorems:
                continue
            count += len(theorems)
            for theorem, axioms in axioms_of_many(module, theorems).items():
                extra = axioms - ALLOWED
                if not extra:
                    continue
                if extra <= KNOWN.get(theorem, set()):
                    known.append((theorem, sorted(extra)))
                else:
                    bad.append((theorem, sorted(extra)))
        for theorem, extra in known:
            print(f"KNOWN: {theorem} also depends on {', '.join(extra)} (documented)")
        for theorem, extra in bad:
            print(f"DIRTY: {theorem} depends on {', '.join(extra)}")
        if bad:
            print(f"{len(bad)} dirty of {count} theorems")
            return 1
        print(f"OK: all {count} theorems, {len(known)} documented exception(s)")
        return 0

    if args.md:
        print("| # | Module | Headline theorem | Axioms |")
        print("|---|---|---|---|")
        for n, (module, theorem) in enumerate(THEOREMS, start=1):
            axes = axioms_of(module, theorem)
            if axes is None:
                status = "missing"
            elif axes - ALLOWED:
                status = ", ".join(sorted(axes - ALLOWED))
            else:
                status = ", ".join(sorted(axes)) or "none"
            print(f"| {n} | `{module}` | `{theorem.split('.')[-1]}` | {status} |")
        return 0

    entries = list(THEOREMS)
    for item in args.also:
        module, theorem = item.split(",", 1)
        entries.append((module, theorem))

    # One Lean run per theorem: some stages define the same helper name
    # (`dotRange` in GemmLoop and GemmMemoryLoop), so the modules cannot all be
    # imported into a single environment.
    missing: list[str] = []
    failures: list[tuple[str, list[str]]] = []
    known: list[tuple[str, list[str]]] = []
    for module, theorem in entries:
        result = axioms_of(module, theorem)
        if result is None:
            missing.append(theorem)
            continue
        extra = result - ALLOWED
        if not extra:
            continue
        expected = KNOWN.get(theorem, set())
        if extra <= expected:
            known.append((theorem, sorted(extra)))
        else:
            failures.append((theorem, sorted(extra - expected)))

    for theorem in missing:
        print(f"MISSING: {theorem} produced no axiom report")
    for theorem, extra in known:
        print(f"KNOWN: {theorem} also depends on {', '.join(extra)} (documented)")
    for theorem, extra in failures:
        print(f"DIRTY: {theorem} depends on {', '.join(extra)}")
    if missing or failures:
        print(f"{len(missing)} missing, {len(failures)} dirty of {len(entries)}")
        return 1

    print(f"OK: {len(entries)} theorems, {len(known)} documented exception(s), "
          f"axioms within {{{', '.join(sorted(ALLOWED))}}}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
