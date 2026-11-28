# SYCL-TLA FMHA prefill: gap analysis and proposal

Status: proposal for stages 247+. The GEMM stack (stages 174–245) is merged
on `main`; this document scopes the next kernel family: the SYCL-TLA FMHA
prefill (`XeFMHAFwdKernel`, BF16, head dim 128).

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
  8x8x16 atom), all with `null` as the second accumulator; 40 carry
  `{Atomic}` and 24 do not;
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

- **1813 statements decode (92.3%)** with the GEMM stack as is;
- **152 statements (7.7%) do not**:

| Form | Count | Why it fails today |
| --- | --- | --- |
| `sel` (plain, `(W) sel`, `(f3.1) sel`) | 66 | no `sel` decoder |
| `mad` with a negated source (`-rN.M<...>`) | 40 | source parser has no unary `-` |
| `math.exp` | 33 | no math decoder |
| `sync.allwr` | 8 | `sync` classifier knows nop/allrd/bar only |
| `mov ... 0x76543210:v` | 1 | `.v` immediate width not parsed |
| `cmp` (plain) | 1 | only predicated `cmp` is decoded |
| `not` (plain) | 1 | no `not` opcode |
| `bfn.(s0&s1|~s0&s2)` | 1 | third bfn mask form |
| `math.inv` | 1 | no math decoder |

Everything else — 878 mov, 273 mul, 159 add, 49 mad, the predicated and plain
block2d loads/stores (`d32t`, `d16v`, `d16`, `d32x16t`, `d32x32t`, `d32x64t`),
`jmpi`, `send.gtwy`, `bfn`, `mach`/`macl` and the DPAS forms — already
decodes.

## 4. Semantic gaps

Decoding is only 7.7% of the work; the new semantics are:

1. **Select and predicates**: `sel` with `(ge)f0.0`-style conditions and plain
   selects, on `d`/`ud` operands.
2. **Negated sources**: `-rN.M<...>` as `0 - rN.M` (and `-imm`), used 40 times.
3. **Scalar math**: `math.exp`, `math.inv` (and `math.log` in the LSE variant).
   These are MUFU approximations, not exact IEEE operations: the model needs a
   value function plus a relative/absolute error budget, and the end-to-end
   theorem must be tolerance-based.
4. **`sync.allwr`**: an all-write scoreboard wait; extends the `sync` classes
   and the ordering story of stage 228.
5. **DPAS with a `null` second accumulator and the `Atomic` flag**: 64 forms,
   8x8x16 BF16 atom (the same atom as the GEMM), second accumulator unused,
   and the flag recorded but its arithmetic meaning to be confirmed (both
   dumps accumulate; `Atomic` appears in 40 of 64 forms).
6. **Row softmax**: row max via `cmp`/`sel`, `exp`, sum, reciprocal, scale —
   the fp32 softmax pipeline.
7. **Online softmax over KV tiles**: running max `m`, denominator `l`, and
   `O ← O * exp(m_old − m_new) + P·V` rescaling, with the accumulator living
   across the KV-tile loop.
8. **Causal masking**: `sel`/`cmp` build the mask on the diagonal tile; the
   theorem must state exactly which `(q, k)` pairs contribute.
9. **P conversion**: fp32 softmax block → BF16 before the second DPAS.
10. **Epilogue**: normalize by `1/l` and store `O` (and `log2(l)` for LSE),
    including the `store.ugm`/`store_block2d` mix.
11. **Reconvergence**: `join`/`goto` appear in the dump (8 each); the model
    needs a reconvergence story for the divergent mask tiles.

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

| Stage | Deliverable | Acceptance |
| --- | --- | --- |
| 247 | Import the prefill dump (`fmhaPrefillRaw`, sha256 provenance) and prove the coverage census above | 1965 statements, 1813/152 split, counts per form |
| 248 | Negated sources (`-rN`, `-imm`) and `.v` immediates | the 41 `mad`/`mov` forms decode; GEMM regression stays green |
| 249 | `sel` decoder and value semantics (plain and predicated conditions) | 66 forms decode; select laws (truth table, lane frame) |
| 250 | Plain `cmp`, `not`, `bfn.(s0&s1|~s0&s2)` | the 3 remaining scalar forms decode |
| 251 | `sync.allwr` class + scoreboard ordering | 8 forms classified; ordering law vs the `sync.nop` model |
| 252 | `math.exp`/`math.inv` model with an error budget | value laws, monotonicity, hardware-derived samples |
| 253 | Row-softmax algebra (max, exp, sum, reciprocal) | softmax value theorem on a full row |
| 254 | Online-softmax invariant and KV-tile rescaling | fold theorem: running (m, l, O) equals two-pass softmax |
| 255 | Causal mask theorem | exact (q, k) contribution set on the diagonal tile |
| 256 | QK^T DPAS phase (64 atoms, null acc1) | slab sum over the attention tiles; null-accumulator handling |
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
