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
    "IntelGpu.realGemm_not_decoded": {"Classical.choice"},
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
    ("Intel.RealGemmCoverage", "IntelGpu.realGemm_not_decoded"),
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
