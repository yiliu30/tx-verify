# Response to review #63

This file maps each item of review #63 to the stages and artifacts that address
it, and separates what is proved from what remains trusted or open. The stage
numbering continues the original 61-stage stack; the PRs are in the staging
fork.

## Priority map

| Review item | Stages (PRs) | Evidence | Status |
| --- | --- | --- | --- |
| P0 real assembly import | 62 (#64), 65 (#67), 82 (#84), 83 (#85), 174, 183, 185 | four real dumps (add-one, integer GEMM, loop vector add, straight-line vector add) with sha256 provenance and generated statement lists; the FMHA DPAS line in 79 (#81); the raw SYCL-TLA 256x256x32 BF16 GEMM dump with 2252 statements and 32 DPAS; a total decoder for that dump (stage 175) a census of its 968 predicated forms (stage 183) and structured decoding of all 377 predicated moves (stage 185) | addressed for these kernels; the SYCL-TLA dump is imported and total-decoded, but not yet connected to execution semantics |
| P0 reject unsupported explicitly | 62b (#64), 63 (#65), 82 (#84), 92 | `rejected`, `realGemm_rejectedOps`, `realVectorAdd_rejectedOps`, the fail-closed `parseExec` mask check, `masked_mov_decodes` and `parseExec_rejects_M9` | addressed; all dumps are all-or-nothing |
| P0 unified semantics | 63-67 (#65-#69), 68-77 (#70-#79), 83-85 (#85-#87), 104-113, 204-209 | one `RInstr`/`stepWith` model; `realAddOne_effect`, `realGemm_output`, `realVectorAdd_effect`; loop vector-add tables, index, body effect, per-lane CF and decoded branch sites; the SYCL-TLA loop-tail counter increments with their value and frame laws the loop-exit comparison with its flag semantics the composed loop-tail transition with both outcomes the iteration theorems for continuing and exiting runs the mainloop iteration composing the DPAS phase with the loop tail under the DPAS register frame, the back-edge/exit targets and the lifted iteration theorems | addressed for the modeled slots; predicate-value composition remains |
| P0 GRF and SIMD | 64 (#66), 66 (#68), 68 (#70), 83 (#85), 90-98, 103, 105, 107, 112, 141, 151, 186, 187, 188, 189, 190, 191, 192, 193 | regions, aliases, execution sizes in `Grf`/`gemmAlias`; per-lane predicates, predicated `sel`, predicate `and`/`or`, register comparisons, both predicated gotos; M1-M8 masks, all six masked moves, frame laws, a wrong-mask negative test, correct destination `<hstride>` parsing, dword/qword view laws, the 24-lane pack layout and a per-lane CF interpreter; generic active-window, operand-index, write-coverage and commutation laws; mask-aware add/load/store execution for the loop body with full-mask agreement and frame laws; execution of the SYCL-TLA predicated moves with destination frames and a proved entry block; a structured decoder and execution for the prologue `and`/`add`/`mad` forms, with a total parser for all 109 ALU forms, a destination-class census, 54 executed ALU forms and a multi-bank `acc`/`a`/`cr` state | addressed for the modeled loop body and the TLA moves; general instruction-level mask dispatch outside these classes remains |
| P0 SEND and SBID | 78 (#80), 147 | `issueLoad`/`issueStore`/`wait`/`commitLoad`, `loadPipeline_value`, `storePipeline_value`, `addOnePipeline_value`; one transcribed descriptor layout with SBID extraction, distinct-token progression and out-of-range rejection | mechanism modeled; the SBID bit layout is a documented transcription assumption because the dumps do not print the field |
| P1 memory and concurrency | 60, 64 (#66), 67 (#69), 106, 139, 152, 153, 154, 157, 162, 167, 168, 169, 194, 199, 200 | word/byte memory, alignment, `load32LE_store32LE_*`, `realAddOne_byteRangesDisjoint`, per-lane stores and frames, real loop-body `load/add/store` effect; a per-location visibility model with release/acquire message passing; global/SLM address-space disjointness and workgroup-barrier SLM visibility; cross-lane C-address disjointness from launch-id injectivity, a composed 32-lane store result and a write-through workgroup cache; two-cache broadcast-invalidation traffic; a directory with ownership transfer and sharer invalidation; relaxed/release/acquire/seq_cst store buffers; write-back dirty lines, eviction and FIFO request queues; an SLM bank-conflict/swizzle model; decoded block2d load/store forms, their parsed address operands, effective addresses and a tile-memory load/store semantics | partial: no hardware address aliasing or arbitration/dual-port effects; the cache, store-buffer and bank models are separate; the tile memory abstracts swizzles and row geometry |
| P1 DPAS refinement | 49, 50, 79 (#81), 86 (#88), 99-101, 142, 150, 174, 176, 177, 179, 180, 181, 182, 184, 197, 201 | decoded `dpas.8x8`; `fmhaFp8Atom` 8x8x32 vs `tlaXeF16Atom` 8x16x16; atom counts 1 vs 2; packed A/B/C layouts, collision-free addresses and decoded register bases; value equality with one depth-32 slab, K=16 split, 2x1/2x2 tile composition and register-level execution at the decoded bases; a census of the 32 BF16 DPAS instructions in the real SYCL-TLA GEMM and register-level execution of each DPAS step, a two-step accumulation proof and a BF16-to-slab value bridge and packed-register half extraction and the full 32-step slab sum for both accumulator blocks, a BF16-decoded 32-step chain, the decoded mainloop block bounds, the classified mainloop schedule with the barrier after all DPAS and the unique back-edge at PC 1404, the mainloop DPAS phase instantiation of the slab sum and the plain block2d loads whose `r64:16`/`r80:16`/`r96:16`/`r112:16`/`r30:31` windows cover every DPAS A/B base | addressed for the coded 8x8x32 layout and the real DPAS forms; the full 32-step sum and physical tile packing remain |
| P1 numerical semantics | 27-31, 43-56, 61, 80 (#82), 149, 156, 159, 164, 166, 170, 171, 172, 178 | fixed-point bounds, NaN payload propagation, `vstepIEEE` with `0 * inf = NaN`; exact-grid fp16 addition, ties-to-even and a single-rounding encode/decode path; total fp16 decode, signed zeros, subnormal crossings, the overflow threshold, NaN/Inf propagation and directed rounding with an exact overflow table; general per-binade RNE for every finite sum below the overflow threshold; sticky exception flags for the fp16 add path; a fused multiply-add with one RNE, ties-to-even and special-value flags; sticky per-lane flags folded over lanes and iterations; directed-rounding FMA with an exact overflow table; a BF16 bit decode and pair split for the SYCL-TLA DPAS sources | partial: hardware traps, trap delivery, FTZ/DAZ and tininess-before-rounding remain outside the proved class |
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
  `lake build Intel` (169 jobs) and `Tools/check_axioms.py --all`
  (2006 theorems, 536 documented exceptions at stage 209).
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
  sticky exception flags, sticky per-lane flag accumulation and a fused
  multiply-add and directed-rounding FMA; hardware traps, trap delivery,
  FTZ/DAZ and tininess-before-rounding remain;
- caches: stages 154, 157 and 162 model write-through caches with invalidate,
  broadcast traffic and a directory/ownership protocol; stage 167 models
  relaxed/release/acquire/seq_cst store buffers; stage 168 adds write-back
  dirty lines, eviction and request queues; stage 169 models SLM bank
  conflicts and XOR swizzling; hardware address aliasing and arbitration
  effects remain;
- SBID assignments are a documented transcription assumption (stage 147),
  because the dumps do not print the field.

## Stage index 137-172

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
| 165 | #167 | review stage map refresh |
| 166 | #168 | fp exception flags |
| 167 | #169 | relaxed atomics and store buffers |
| 168 | #170 | write-back caches and request queues |
| 169 | #171 | SLM banks and swizzling |
| 170 | #172 | fp16 fused multiply-add |
| 171 | #173 | sticky per-lane flags |
| 172 | #174 | directed-rounding FMA |
| 173 | #175 | review stage map refresh |
| 174 | #176 | real SYCL-TLA GEMM import |
| 175 | #177 | total decoder for the SYCL-TLA dump |
| 176 | #178 | register-level execution of the SYCL-TLA DPAS chain |
| 177 | #179 | composing two SYCL-TLA DPAS steps |
| 178 | #180 | BF16 source decode |
| 179 | #181 | BF16 values in the DPAS slab |
| 180 | #182 | packed BF16 register halves |
| 181 | #183 | the full 32-step DPAS sum |
| 182 | #184 | the second accumulator |
| 183 | #185 | census of the predicated forms |
| 184 | #186 | the DPAS chain over BF16 values |
| 185 | #187 | decoding the predicated moves |
| 186 | #188 | executing the predicated moves |
| 187 | #189 | sequencing moves and the entry effect |
| 188 | #190 | decoding the predicated ALU forms |
| 189 | #191 | executing the prologue ALU |
| 190 | #192 | ALU parsed/rejected census |
| 191 | #193 | all ALU destinations |
| 192 | #194 | more register-destination ALU ops |
| 193 | #195 | multi-bank ALU state |
| 194 | #196 | block2d memory forms |
| 195 | #197 | control and scoreboard forms |
| 196 | #198 | control-flow targets |
| 197 | #199 | mainloop bounds |
| 198 | #200 | mainloop block census |
| 199 | #201 | block2d address operands |
| 200 | #202 | block2d address semantics |
| 201 | #203 | mainloop operand-window loads |
| 202 | #204 | mainloop DPAS phase |
| 203 | #205 | mainloop schedule |
| 204 | #206 | loop-tail counters |
| 205 | #207 | loop-exit comparison |
| 206 | #208 | loop tail |
| 207 | #209 | loop iteration |
| 208 | #210 | mainloop iteration |
| 209 | #211 | loop structure and mainloop iteration |

The stack is intentionally one PR per stage (#64-#211), as requested. The
review's consolidation suggestion is left as a merge/upstreaming decision.
