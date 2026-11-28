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
    ("Intel.GemmSlmCompute", "IntelGpu.gemmTile_executed"),
    ("Intel.Dpas", "IntelGpu.dpasRun_correct"),
    ("Intel.GemmDpasLoop", "IntelGpu.dpasProg_correct"),
    ("Intel.TlaInstance", "IntelGpu.tlaXeF16_gemm_spec"),
    ("Intel.DpasMask", "IntelGpu.tlaXeF16_gemm_spec_tail"),
    ("Intel.Epilogue", "IntelGpu.gemmTile_end_to_end"),
    ("Intel.EpilogueLd", "IntelGpu.epilogueLd_correct"),
    ("Intel.EpilogueFrame", "IntelGpu.epilogueLd_frame"),
    ("Intel.GemmAssembly", "IntelGpu.tlaXeF16_gemm_executed"),
    ("Intel.Staging", "IntelGpu.stageSlab_correct"),
    ("Intel.Mainloop", "IntelGpu.mainloop_correct"),
    ("Intel.LaneStaging", "IntelGpu.laneBlock_value"),
    ("Intel.TilePipeline", "IntelGpu.mainloop_epilogue"),
    ("Intel.Numeric", "IntelGpu.maccDot_error"),
    ("Intel.Rounding", "IntelGpu.truncDot_error"),
    ("Intel.RoundingNearest", "IntelGpu.roundDot_error"),
    ("Intel.RoundingEven", "IntelGpu.evenDot_error"),
    ("Intel.NumericBridge", "IntelGpu.wpDot_error"),
    ("Intel.Exactness", "IntelGpu.evenDot_exact_on_grid"),
    ("Intel.Fp16Shape", "IntelGpu.fp16_grid_exact_of_exp"),
]

LINE = re.compile(r"^'(?P<name>[^']+)' depends on axioms: \[(?P<axioms>[^\]]*)\]")


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
    args = parser.parse_args()

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
