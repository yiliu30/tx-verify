# Hardware conformance: the SYCL-TLA BF16 FMHA prefill

This note records the hardware evidence for the SYCL-TLA FMHA prefill kernel
whose assembly is imported in `Intel/Examples/RealFmhaPrefill.lean`
(1946 instructions, 1965 statements, sha256 provenance in that file).

## Kernel and run

- kernel: `XeFMHAFwdKernel` (SYCL-TLA flash attention), BF16 inputs with FP32
  accumulator, `head_size_qk = head_size_vo = 128`, batch 1, one Q/KV head;
- build: oneAPI 2026.1, IGC shader dump enabled with the standard dump
  environment (`IGC_ShaderDumpEnable=1`, `NEO_CACHE_PERSISTENT=0`,
  `NEOReadDebugKeys=1`, `RebuildPrecompiledKernels=1`);
- shape: `seq_len_qo = seq_len_kv = 256`, non-causal, one iteration;
- the LSE variant was used for the verification run.

## Result

- full output vs the device reference: **Passed**;
- LSE vs a host log-sum-exp reference: **max abs error `1.5e-05`**
  (tolerance-based, not bit-exact).

The plain prefill runner's built-in `--verify=1` is broken on this host: the
kernel returns `kErrorInternal` and the reference buffer stays zero. The LSE
runner is the pinned harness until that is fixed upstream.

## Relation to the Lean model

`Intel/TlaMath.lean` models `math.exp`/`math.inv` as a `MufuModel`: bit-level
functions plus a rational contract (`expErr`, `invErr`, monotonicity). The
contract fields are parameters, so every theorem that consumes a budget shows
it in its statement. The `1.5e-05` end-to-end LSE measurement is the current
budget evidence for the composed softmax; per-op MUFU samples (exp/inv over a
dense input grid) still need a microbenchmark run and will refine the
`expErr`/`invErr` instantiation used by the stage-258 conformance theorem.

Product names and host details are withheld per the project's policy.


## LSE prefill run

A second run used the LSE prefill binary (`06_xe_fmha_fwd_lse`,
`head_size_qk = head_size_vo = 128`, batch 1, 1 Q/KV head, 256x256) on the
same lab GPU family:

- compiler: oneAPI 2025.3 IGC (Xe2);
- `Full kernel (LSE) output vs reference`: **Passed**;
- `LSE output vs host log-sum-exp reference`: **Passed**, max abs error
  **`1.52588e-05`**;
- `Sequence-parallel (1 chunks) combined vs reference`: **Passed**.

The assembly of this binary is imported in `Intel/Examples/RealFmhaLse.lean`
(2581 instructions / 2694 statements, sha256 provenance there) and
`Intel/FmhaLseCoverage.lean` proves 2694/2694 decode and execution.
