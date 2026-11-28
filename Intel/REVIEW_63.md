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
| P0 GRF and SIMD | 64 (#66), 66 (#68), 68 (#70), 83 (#85), 90-98, 103, 105, 107, 112, 141, 151 | regions, aliases, execution sizes in `Grf`/`gemmAlias`; per-lane predicates, predicated `sel`, predicate `and`/`or`, register comparisons, both predicated gotos; M1-M8 masks, all six masked moves, frame laws, a wrong-mask negative test, correct destination `<hstride>` parsing, dword/qword view laws, the 24-lane pack layout and a per-lane CF interpreter; generic active-window, operand-index, write-coverage and commutation laws; mask-aware add/load/store execution for the loop body with full-mask agreement and frame laws | addressed for the modeled loop body; general instruction-level mask dispatch outside these classes remains |
| P0 SEND and SBID | 78 (#80), 147 | `issueLoad`/`issueStore`/`wait`/`commitLoad`, `loadPipeline_value`, `storePipeline_value`, `addOnePipeline_value`; one transcribed descriptor layout with SBID extraction, distinct-token progression and out-of-range rejection | mechanism modeled; the SBID bit layout is a documented transcription assumption because the dumps do not print the field |
| P1 memory and concurrency | 60, 64 (#66), 67 (#69), 106, 139, 152, 153, 154, 157, 162, 167, 168 | word/byte memory, alignment, `load32LE_store32LE_*`, `realAddOne_byteRangesDisjoint`, per-lane stores and frames, real loop-body `load/add/store` effect; a per-location visibility model with release/acquire message passing; global/SLM address-space disjointness and workgroup-barrier SLM visibility; cross-lane C-address disjointness from launch-id injectivity, a composed 32-lane store result and a write-through workgroup cache; two-cache broadcast-invalidation traffic; a directory with ownership transfer and sharer invalidation; relaxed/release/acquire/seq_cst store buffers; write-back dirty lines, eviction and FIFO request queues | partial: no bank conflicts or hardware address aliasing; the cache and store-buffer models are separate |
| P1 DPAS refinement | 49, 50, 79 (#81), 86 (#88), 99-101, 142, 150 | decoded `dpas.8x8`; `fmhaFp8Atom` 8x8x32 vs `tlaXeF16Atom` 8x16x16; atom counts 1 vs 2; packed A/B/C layouts, collision-free addresses and decoded register bases; value equality with one depth-32 slab, K=16 split, 2x1/2x2 tile composition and register-level execution at the decoded bases | addressed for the coded 8x8x32 layout; physical tile packing remains a model assumption |
| P1 numerical semantics | 27-31, 43-56, 61, 80 (#82), 149, 156, 159, 164, 166 | fixed-point bounds, NaN payload propagation, `vstepIEEE` with `0 * inf = NaN`; exact-grid fp16 addition, ties-to-even and a single-rounding encode/decode path; total fp16 decode, signed zeros, subnormal crossings, the overflow threshold, NaN/Inf propagation and directed rounding with an exact overflow table; general per-binade RNE for every finite sum below the overflow threshold; sticky exception flags for the fp16 add path | partial: not a full IEEE FMA; hardware traps, sticky lane state, FTZ/DAZ and fused multiply-add remain outside the proved class |
| P1 hardware conformance | 81 (#83) | GPU vs `gemmDot`: `C00=-2 C11=-5 C6363=4 checksum=4294967290 bad=0`; add-one and vector-add runs | addressed at source level; the GEMM dump was compiled with a different compiler minor version |
| P2 complex kernels | 79 (#81), 82-85 (#84-#87), 99-102, 148, 150, 155, 163 | real FMHA DPAS decoded, packed and smoke-tested; real straight-line vector add end-to-end; E4M3 decode and an fp8 atom value path | open: full FMHA/SageAttention execution; the decoded atom, a T-step register-level mainloop and a zero-padded tail are modelled, but physical packing, masked/partial DPAS behavior and the rest of the kernel remain |

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
  `lake build Intel` (131 jobs) and `Tools/check_axioms.py --all`
  (1519 theorems, 393 documented exceptions at stage 168).
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
- M1-M8 and `_NM` masks are decoded into `Exec`; masked moves and the loop
  body's add/load/store have mask-aware execution (stages 141, 151);
- the scaled memory decoder accepts only the `0x4*index` form;
- the loop-back writeback packs dwords into `V0059`, while the body load reads
  qword lanes; `vaLoopLoopBack_dword_counterexample` shows the existing model
  does not literally identify the two views. Stage 160 adds an explicit
  `coalesceReg59` adapter and proves the literal second iteration; it does not
  change the raw semantics.

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

- masked/predicated loop vector add: predicate logic, both predicated `goto`s,
  the false-lane memory frame and generic mask laws are stages 130-151; the
  decoded PC 36-43 loop-back block and its value-level second iteration are
  stage 158. The dword/qword aliasing gap is bridged by the explicit
  coalescing adapter of stage 160, which proves the literal second-iteration
  store; a multi-iteration induction and the all-32-lane extension remain;
- FMHA/SageAttention execution: the 8x8x32 DPAS value path, the fp8 E4M3
  element path, one register-level DPAS step and a T-step register-level
  mainloop and a zero-padded tail are modelled (stages 142, 148, 150, 155,
  163); physical tile packing, masked/partial DPAS behavior, the rest of the
  kernel and hardware validation remain;
- full IEEE semantics: stages 149, 156, 159 and 164 cover exact-grid fp16
  addition, ties-to-even, signed zeros, subnormal crossings, the overflow
  threshold, NaN/Inf propagation, directed rounding, general per-binade RNE
  and sticky exception flags; hardware traps, FTZ/DAZ and a full IEEE FMA
  remain;
- caches: stages 154, 157 and 162 model write-through caches with invalidate,
  broadcast traffic and a directory/ownership protocol; stage 167 models
  relaxed/release/acquire/seq_cst store buffers; stage 168 adds write-back
  dirty lines, eviction and request queues; bank conflicts and hardware
  address aliasing remain;
- SBID assignments are a documented transcription assumption (stage 147),
  because the dumps do not print the field.

## Stage index 137-164

| Stage | PR | Result |
| --- | --- | --- |
| 137 | #139 | memory effect through the decoded path |
| 138 | #140 | real P3/P6 guards from the decoded prefix |
| 139 | #141 | per-location visibility and release/acquire |
| 140 | #142 | PC 0 preamble and kernel effect from PC 0 |
| 141 | #143 | generic execution-mask laws |
| 142 | #144 | FMHA atom value refinement and tile composition |
| 143 | #145 | predicated lanes write nothing |
| 144 | #146 | reach `ret` with `halted = true` |
| 145 | #147 | global/SLM disjointness and workgroup barriers |
| 146 | #148 | grid-stride indices and store composition |
| 147 | #149 | SBID fields in an encoded descriptor |
| 148 | #150 | fp8 E4M3 decode for the FMHA atom |
| 149 | #151 | restricted IEEE fp16 addition rounding |
| 150 | #152 | register-level FMHA DPAS execution |
| 151 | #153 | mask-aware add/load/store for the loop body |
| 152 | #154 | cross-lane race freedom |
| 153 | #155 | composed 32-lane workgroup store result |
| 154 | #156 | write-through cache coherence |
| 155 | #157 | register-level T-step FMHA mainloop |
| 156 | #158 | fp16 special values and overflow |
| 157 | #159 | two-cache coherence traffic |
| 158 | #160 | decoded PC 36-43 loop-back block |
| 159 | #161 | directed fp16 rounding |
| 160 | #162 | dword/qword coalescing adapter |
| 161 | #163 | n-iteration grid-stride induction |
| 162 | #164 | directory/ownership coherence |
| 163 | #165 | FMHA tail and partial K |
| 164 | #166 | general fp16 round-to-nearest-even |

The stack is intentionally one PR per stage (#64-#166), as requested. The
review's consolidation suggestion is left as a merge/upstreaming decision.
