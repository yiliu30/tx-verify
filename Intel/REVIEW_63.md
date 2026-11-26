# Response to review #63

This file maps each item of review #63 to the stages and artifacts that address
it, and separates what is proved from what remains trusted or open. The stage
numbering continues the original 61-stage stack; the PRs are in the staging
fork.

## Priority map

| Review item | Stages (PRs) | Evidence | Status |
| --- | --- | --- | --- |
| P0 real assembly import | 62 (#64), 65 (#67), 82 (#84), 83 (#85) | four real dumps (add-one, integer GEMM, loop vector add, straight-line vector add) with sha256 provenance and generated statement lists; the FMHA DPAS line in 79 (#81) | addressed for these kernels |
| P0 reject unsupported explicitly | 62b (#64), 63 (#65), 82 (#84), 92 | `rejected`, `realGemm_rejectedOps`, `realVectorAdd_rejectedOps`, the fail-closed `parseExec` mask check, `masked_mov_decodes` and `parseExec_rejects_M9` | addressed; all dumps are all-or-nothing |
| P0 unified semantics | 63-67 (#65-#69), 68-77 (#70-#79), 83-85 (#85-#87), 104-113 | one `RInstr`/`stepWith` model; `realAddOne_effect`, `realGemm_output`, `realVectorAdd_effect`; loop vector-add tables, index, body effect, per-lane CF and decoded branch sites | addressed for the modeled slots; predicate-value composition remains |
| P0 GRF and SIMD | 64 (#66), 66 (#68), 68 (#70), 83 (#85), 90-98, 103, 105, 107, 112, 141 | regions, aliases, execution sizes in `Grf`/`gemmAlias`; per-lane predicates, predicated `sel`, predicate `and`/`or`, register comparisons, both predicated gotos; M1-M8 masks, all six masked moves, frame laws, a wrong-mask negative test, correct destination `<hstride>` parsing, dword/qword view laws, the 24-lane pack layout and a per-lane CF interpreter; generic active-window, operand-index, write-coverage and commutation laws | partial: masked moves execute with lane offsets, but other instructions do not yet consume `Exec`; decoded branch composition is stages 130-138 |
| P0 SEND and SBID | 78 (#80) | `issueLoad`/`issueStore`/`wait`/`commitLoad`, `loadPipeline_value`, `storePipeline_value`, `addOnePipeline_value` | mechanism modeled; exact SBIDs are not printed and remain assumptions |
| P1 memory and concurrency | 60, 64 (#66), 67 (#69), 106, 139 | word/byte memory, alignment, `load32LE_store32LE_*`, `realAddOne_byteRangesDisjoint`, per-lane stores and frames, real loop-body `load/add/store` effect; a per-location visibility model with release/acquire message passing | partial: cacheless model with full fences; no caches, relaxed atomics or SLM aliasing |
| P1 DPAS refinement | 49, 50, 79 (#81), 86 (#88), 99-101, 142 | decoded `dpas.8x8`; `fmhaFp8Atom` 8x8x32 vs `tlaXeF16Atom` 8x16x16; atom counts 1 vs 2; packed A/B/C layouts, collision-free addresses and decoded register bases; value equality with one depth-32 slab, K=16 split and 2x1/2x2 tile composition | addressed for the coded 8x8x32 layout |
| P1 numerical semantics | 27-31, 43-56, 61, 80 (#82) | fixed-point bounds, NaN payload propagation, `vstepIEEE` with `0 * inf = NaN` | partial: not a full IEEE FMA |
| P1 hardware conformance | 81 (#83) | GPU vs `gemmDot`: `C00=-2 C11=-5 C6363=4 checksum=4294967290 bad=0`; add-one and vector-add runs | addressed at source level; the GEMM dump was compiled with a different compiler minor version |
| P2 complex kernels | 79 (#81), 82-85 (#84-#87), 99-102 | real FMHA DPAS decoded, packed and smoke-tested; real straight-line vector add end-to-end | open: full FMHA/SageAttention execution and low-precision paths |

## Acceptance criteria

- Capture real unmodified IGC assembly: stages 62, 65, 82, 83.
- Record provenance and check the decoded program: hashes in the modules;
  `realAddOne_decoded_eq`, `realGemm_preamble_prefix`, `realVectorAddFlat_decoded_eq`.
- Execute with formal ISA semantics (address, predicates, memory, EOT/ret):
  `realAddOne_effect`, `realGemm_output`, `realVectorAdd_effect`.
- Memory safety, correct output, frame, race freedom, termination: the three
  effect theorems above, with alignment, bounds and distinct-address
  hypotheses stated explicitly.
- Reproducible hardware/model comparison and negative tests:
  `Tools/conformance/`, plus the decoder rejection theorems.
- Build and full axiom audit in CI, assumptions separate:
  `lake build Intel` (77 jobs) and `Tools/check_axioms.py --all`
  (648 theorems, 228 documented exceptions at stage 142).
- Document the trusted base: below and in `Intel/README.md`.

## Trusted base

Transcribed, not derived from a formal IGC front end:

- the statement lists of the four real dumps, with their sha256 hashes and
  redacted platform/options lines;
- the `.decl` alias, type and element-count tables in `GemmReal`,
  `VectorAdd` and the add-one instance;
- the FMHA DPAS instruction and its operand types in `RealDpas`.

Parser/decoder scope:

- operands are parsed with structural `List Char` helpers; unsupported forms
  return `none`;
- M1-M8 and `_NM` masks are decoded into `Exec`; masked moves apply their
  offsets, other instructions do not yet;
- the scaled memory decoder accepts only the `0x4*index` form.

Model assumptions:

- word-addressed memory with aligned d32 accesses; byte memory is a separate
  refinement;
- per-lane distinct addresses for store frames and race freedom;
- SEND: fair completion, sample-at-issue, register-scoreboard wait, no token
  reuse while pending;
- DPAS: the 8x8x32 and 8x16x16 atom shapes and their K depths;
- numerics: the class model (`Fval`) with NaN payload propagation and
  `0 * inf = NaN`, not a full IEEE FMA.

Logical axioms: `propext` and `Quot.sound` for the proofs; the documented
`Classical.choice` exceptions come from `String.toList` in the decoders and
from `Classical.choose` in the racing-store model.

## Remaining work

- masked/predicated loop vector add: apply `(M5, 16)` execution masks,
  `cmp`/`and`/`or` predicate logic, predicated `goto`, and the grid-stride loop;
- FMHA/SageAttention execution and low-precision paths;
- 8x8x32 DPAS operand packing is modelled; hardware validation of the layout
  and the rest of the FMHA execution path remain;
- full IEEE semantics and a hardware memory model with visibility and
  synchronization;
- exact SBID assignments from the binary encoding.

The stack is intentionally one PR per stage (#64-#99), as requested. The
review's consolidation suggestion is left as a merge/upstreaming decision.
