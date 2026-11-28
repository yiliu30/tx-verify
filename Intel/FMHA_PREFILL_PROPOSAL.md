# SYCL-TLA FMHA prefill: gap analysis and proposal

Status: proposal for stages 247+. The GEMM stack (stages 174–245) is merged
on `main`; this document scopes the next kernel family: the SYCL-TLA FMHA
prefill (`XeFMHAFwdKernel`, BF16, head dim 128). Stages 247 and 248 are
merged (PRs #251, #252, #254, #255, #256, #257, #258, #259, #260, #261,
#262, #263, #265, #266, #267, #268, #269, #270, #271, #272, #273); decoding and execution are total,
and the MUFU contract, softmax pipeline, causal mask, DPAS atoms, QK/PV
chains, RNE conversion, epilogue ratio and pipeline order are proved. The
remaining gaps are listed in section 8.

## 1. Scope

First target: the non-varlen **prefill** kernel for BF16 with
`head_size_qk = head_size_vo = 128`, batch 1, one Q head and one KV head
(GQA = 1), non-causal first, then causal. Out of scope for the first pass:
varlen, paged KV cache, FP8/MXFP KV, GQA/MQA, decode, and the
sequence-parallel LSE combining.

## 2. Evidence gathered

Hardware and dumps (lab GPU, oneAPI 2026.1 IGC):

- prefill kernel `XeFMHAFwdKernel`, non-varlen, BF16, hdim 128:
  1946 instructions (1965 statements with labels), `numGRF=256`,
  `numAcc=8`, `numSWSB=32`;
- 64 `dpas.8x8 (16|M0)` instructions with BF16 sources and FP32
  accumulators (the `XE_DPAS_TT<8, float, bfloat16, bfloat16, float>`
  8x8x16 atom): 4 use `null` as the second accumulator and 60 alias it to
  the first accumulator; 40 carry `{Atomic}` and 24 do not;
- softmax path: 33 `math.exp`, 1 `math.inv` (the LSE variant adds 8
  `math.log`), plus `cmp`/`sel`/`mad` for max, mask and sum;
- 66 `sel`, 69 `sync.nop`, 24 `sync.allrd`, 8 `sync.allwr`, 1 `sync.bar`,
  11 `jmpi`.

Verification harness:

- the LSE prefill runner verifies on this host: full output vs reference
  passes, and LSE vs a host log-sum-exp reference passes with max abs error
  `1.5e-05` — conformance is **tolerance-based**, not bit-exact;
- the plain prefill runner's built-in `--verify=1` is broken on this host
  (kernel returns `kErrorInternal`, reference buffer stays zero), so the
  plan uses the LSE runner and/or an independent host attention reference.

## 3. Measured decoder gap

`Tools/parse_igc.py` on the prefill dump, then the merged classifier
(`decodedAll`) over the 1965 statements:

- **1965 of 1965 statements decode (100%)** after the math stage;
- **no unclassified forms remain**.

The decoder covers 878 mov, 273 mul, 159 add, 49 mad, the predicated and
plain block2d loads/stores (`d32t`, `d16v`, `d16`, `d32x16t`, `d32x32t`,
`d32x64t`), `jmpi`, `send.gtwy`, `bfn`, `mach`/`macl`, the DPAS forms and the
34 math instructions. The stage-247 snapshot had 152 unclassified statements; stage 248
closed the 40 negated-source `mad` forms and the single `.v` immediate, and
stage 249 closed all 66 `sel` forms, stage 250 closed the plain
`cmp`/`not`/`bfn` singletons, stage 251 closed the eight `sync.allwr` waits,
and stage 252 closed the 34 math instructions.

These counts are machine-checked in `Intel/FmhaPrefillCoverage.lean`
(`fmhaPrefill_decoded_count`, `fmhaPrefill_unclassified_count`,
`fmhaPrefill_unclassified_forms`).

### 3.1 Verification contract

Decoding is necessary but not sufficient. For this kernel family,
"the assembly is verified" means all of the following:

- **A. Total decode**: `decodedAll` accepts all 1965 statements.
- **B. Step soundness**: every instruction class has a `tlaStep?` case and a
  theorem that the abstract step implements its specification.
- **C. Composition**: per-phase theorems (QK^T, row softmax, online-softmax
  rescaling, PV, epilogue) compose into one kernel-level statement about the
  attention output and, for the LSE variant, the log-sum-exp.
- **D. Tolerance provenance**: the end-to-end statement is
  `|result - reference| <= eps` where `eps` is built from measured MUFU
  (`exp`/`inv`/`log`) and BF16-rounding error budgets, not assumed.
- **E. Hardware conformance**: a pinned runner reproduces the dump hash and
  passes a host attention reference within the stated tolerance.
- **F. Trusted base**: `lake build Intel` plus `Tools/check_axioms.py --all`,
  with only `Classical.choice` among the axioms and no `sorry`.
- **G. Review artifact**: `visualization/verification.html` shows the FMHA
  pipeline, stage timeline and headline claims.

Every stage below lands as a PR that keeps A–G true for the statements it
covers; partial stages state which rows of the census they close.

### 3.2 Semantic coverage census

Decoder coverage is already 94.4%, but semantic coverage is the real metric.
The proposal adds a second census next to the decoder one: a
`semCensus : List (String × Nat)` that counts statements whose abstract step
is proved (not merely parsed), with theorems
`fmhaPrefill_sem_count` and `fmhaPrefill_sem_forms`. The target is
1965/1965; each stage PR updates both censuses, so progress is a checked
number rather than prose.

## 4. Semantic gaps

Decoding is only 7.7% of the work; the new semantics are:

1. **Select and predicates**: `sel` with `(ge)f0.0`-style conditions and plain
   selects, on `d`/`ud` operands (done in stage 249 as `TlaSel`).
2. **Negated sources**: `-rN.M<...>` as `0 - rN.M` (and `-imm`), used 40 times
   (done in stage 248 as `TlaSrc.negReg`).
3. **Scalar math**: `math.exp`, `math.inv` (and `math.log` in the LSE variant).
   These are MUFU approximations, not exact IEEE operations. Stage 252 adds a
   `MufuModel` with a rational `Spec` (error bounds, monotonicity); the
   end-to-end theorem stays tolerance-based and the measured LSE error
   (`1.5e-05`) is recorded in `Tools/conformance/sycl_tla_fmha.md`.
4. **`sync.allwr`**: an all-write scoreboard wait; extends the `sync` classes
   and the ordering story of stage 228 (done in stage 251 as
   `TlaSyncAllwr`).
5. **DPAS second-accumulator aliasing and the `Atomic` flag**: 64 forms,
   executed with the packed-BF16 slab (`fmhaBf16Slab`) since stage 266,
   8x8x16 BF16 atom (the same atom as the GEMM); the second accumulator is
  either `null` (4 forms) or aliased to the first (60 forms), so the model
  must skip `null` and treat the alias as one accumulation; the flag is
  recorded but its arithmetic meaning is to be confirmed (both dumps
  accumulate; `Atomic` appears in 40 of 64 forms).
6. **Row softmax**: row max via `cmp`/`sel`, `exp`, sum, reciprocal, scale —
   the fp32 softmax pipeline (done in stage 253 as `TlaSoftmax`).
7. **Online softmax over KV tiles**: running max `m`, denominator `l`, and
   `O ← O * exp(m_old − m_new) + P·V` rescaling, with the accumulator living
   across the KV-tile loop (done in stage 254 as `TlaOnlineSoftmax`).
8. **Causal masking**: `sel`/`cmp` build the mask on the diagonal tile; the
   theorem states exactly which `(q, k)` pairs contribute (done in stage 255
   as `TlaMask`).
9. **P conversion**: fp32 softmax block → BF16 before the second DPAS.
10. **Epilogue**: normalize by `1/l` and store `O` (and `log2(l)` for LSE),
    including the `store.ugm`/`store_block2d` mix.
11. **Reconvergence**: `join`/`goto` appear in the dump (8 each); the model
    needs a reconvergence story for the divergent mask tiles.

### 4.1 Design sketch

Working module names, following the GEMM stack conventions:

| Module | Content | Laws |
| --- | --- | --- |
| `Intel/TlaSel.lean` | `SelSrc` (`reg`/`imm`/`negReg`/`acc`), `parseSelSrc`, `readSelSrc`, `tlaSelStep` | select truth table, lane frame, `.d`/`.ud` agreement |
| `Intel/TlaCmpPlain.lean`, `Intel/TlaNot.lean` | plain `cmp`, `not` as `TlaInstr` cases | flag semantics, bitwise laws |
| `Intel/TlaBfnMask.lean` | third `bfn` mask form | mask algebra, agreement with the two existing forms |
| `Intel/TlaSyncAllWrite.lean` | `sync.allwr` class and scoreboard wait | ordering law relative to the stage-228 model |
| `Intel/TlaMufu.lean` | `mufuExp`/`mufuInv`/`mufuLog` with specs and error bounds | value laws, monotonicity, `|mufuExp x - exp x| <= epsExp` |
| `Intel/TlaSoftmax.lean` | row max, sum, reciprocal, scale | `softmaxRow` implementation theorem |
| `Intel/TlaOnlineSoftmax.lean` | running `(m, l, O)` across KV tiles | fold theorem: running state equals two-pass softmax |
| `Intel/TlaMask.lean` | causal mask construction | exact `(q, k)` contribution set |
| `Intel/TlaFmhaPhase.lean` | QK^T slab sum, P→BF16, PV slab sum | null acc1 skip, alias collapse, composed phase formula |
| `Intel/FmhaConformance.lean` | `Close eps x y` and composition lemmas | end-to-end tolerance theorem tied to harness data |

MUFU functions are modeled as total functions with an explicit error budget
rather than as exact IEEE operations; the budget is instantiated from
hardware samples recorded with the dump provenance.

## 5. What carries over from the GEMM stack

- the total decoder and `TlaInstr` structure; `classifyOp`/`tlaStep?` dispatch;
- the address model (`TlaAddr`), register windows (`TlaWindow`), tile memory
  and aliasing laws;
- `dpasSlab`/`tlaDpasRun` and the ordered slab sum, with the FP32-quantum
  rounding model (`f32Quantum`, `dpasAccF32`);
- the block2d load/store semantics and the accumulator-store bridge;
- the sync/barrier placement machinery and the SLM barrier model;
- the FTZ/DAZ, flag and trap models for the numeric epilogue;
- the review, axiom-audit and conformance process (and the visualization).

## 6. Proposed stages

Each stage is one stacked PR with `lake build Intel` and the full axiom audit.
Stages 247-267 are merged (PRs #251, #252, #254, #255, #256, #257, #258, #259, #260, #261, #262, #263, #265, #266, #267, #268, #269, #270, #271, #272, #273).

| Stage | Deliverable | Acceptance |
| --- | --- | --- |
| 247 | Import the prefill dump (`fmhaPrefillRaw`, sha256 provenance) and prove the coverage census above | 1965 statements, 1813/152 split, counts per form |
| 248 | Negated sources (`-rN`, `-imm`) and `.v` immediates | the 41 `mad`/`mov` forms decode; GEMM regression stays green |
| 249 | `sel` decoder and value semantics (plain and predicated conditions) | 66 forms decode; select laws (truth table, lane frame) |
| 250 | Plain `cmp`, `not`, `bfn.(s0&s1\|~s0&s2)` | the 3 remaining scalar forms decode |
| 251 | `sync.allwr` class + scoreboard ordering | 8 forms classified; ordering law vs the `sync.nop` model |
| 252 | `math.exp`/`math.inv` model with an error budget | value laws, monotonicity, hardware-derived samples |
| 253 | Row-softmax algebra (max, exp, sum, reciprocal) | softmax value theorem on a full row |
| 254 | Online-softmax invariant and KV-tile rescaling | fold theorem: running (m, l, O) equals two-pass softmax |
| 255 | Causal mask theorem | exact (q, k) contribution set on the diagonal tile |
| 256 | QK^T DPAS phase (64 atoms, `null`-or-aliased acc1) | slab sum over the attention tiles; null and aliased accumulator handling |
| 257 | P→BF16 conversion, PV DPAS phase, epilogue O/LSE | composed attention formula with the recorded rounding |
| 258 | End-to-end prefill conformance | tolerance-based hardware runs (LSE runner + host reference), dump hash, review/visualization update |

## 7. Risks and open questions

- **MUFU accuracy**: exp/log/inv are approximations; the error budget must be
  measured (the LSE host check gives `1.5e-05` absolute on LSE) and stated,
  not guessed.
- **BF16 P rounding**: the softmax block is converted to BF16 before PV; the
  theorem must be tolerance-based or exact under a rounding hypothesis.
- **`Atomic` DPAS flag**: arithmetic meaning must be confirmed from codegen
  (`Atomic` on 40 of 64 forms; both dumps accumulate).
- **Divergent tiles**: `join`/`goto` reconvergence and mask-tile divergence
  need a small divergence model (the `Parked` model of
  `Intel/Divergence.lean` is the natural base).
- **Reference harness**: the plain prefill runner's built-in verify is broken
  on this host; the plan must pin a working harness (LSE runner or a host
  reference computed from the same deterministic inputs).
- **Shape coverage**: start with 256x256, hdim 128, batch 1, 1 head; extend to
  512/1024 context and causal/non-causal after the core composition.


## 8. Status after stage 258 and remaining gaps

Proved on the imported dump: total decoding (1965/1965), the `sel`/`cmp`/
`not`/`bfn`/`sync.allwr`/`math` step semantics, the MUFU contract, row
softmax normalisation, the online-softmax fold invariant, the causal
contribution set, the 64 DPAS atoms with null/aliased second accumulators,
the fixed-accumulator PV chain and the epilogue ratio.

Still open:

- **QK^T chain composition**: the DPAS-only chain is done in stage 259
  (`TlaFmhaQk`); each of the four blocks is its initial value plus eight
  slabs. The real schedule reloads A/B between short groups, so the
  program-level composition with the loads is still open.
- **RNE P→BF16**: the packing views exist, but the rounding conversion from
  FP32 softmax values to BF16 is not modelled yet.
- **LSE variant**: the imported dump is the non-LSE prefill; the LSE build
  adds 8 `math.log` instructions and needs a `log` model plus the `log2(l)`
  epilogue.
- **Per-op MUFU samples**: the end-to-end LSE error (1.5e-05) is recorded;
  the per-op `expErr`/`invErr` budgets still need a microbenchmark.
- **Plain runner**: its `--verify=1` path is broken on the lab host
  (`kErrorInternal`, zero reference); the LSE runner is the pinned harness.
- **Shapes and variants**: 256x256 only; varlen, paged KV, FP8/MXFP, GQA/MQA
  and decode remain out of scope.
