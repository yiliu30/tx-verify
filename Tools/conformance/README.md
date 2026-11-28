# Hardware conformance: the real integer GEMM

This directory records a differential test between an actual Intel GPU run of
the 64x64x64 integer GEMM and the Lean model's evaluated `gemmDot`.

## Inputs

Both sides use the same deterministic inputs:

- `A[i] = (i % 7) - 3` for `i < 64*64`
- `B[i] = (i % 5) - 2` for `i < 64*64`
- `C[i*64+j] = sum_k A[i*64+k] * B[k*64+j]`, 32-bit wrapping.

## Hardware side

`gemm_conformance.cpp` is the same SYCL program shape as the dump (one
work-item per output, a `#pragma unroll 1` K loop). It also checks every output
against a CPU reference and prints a 32-bit checksum.

Build and run with oneAPI:

```
source /opt/intel/oneapi/setvars.sh
icpx -fsycl -O2 gemm_conformance.cpp -o gemm_conformance
SYCL_DEVICE_FILTER=level_zero:gpu ./gemm_conformance
```

Recorded run:

```
C00=-2 C11=-5 C6363=4 checksum=4294967290 bad=0
```

- compiler: Intel oneAPI DPC++/C++ 2026.2.0 (2026.2.0.20261001)
- runtime: oneAPI Unified Runtime over Level-Zero V2, 1.18.40867
- OpenCL driver: 26.45.40867
- device: an Intel discrete GPU; product and PCI details are withheld per the
  project's policy. The dump itself was produced by oneAPI 2026.1, so this run
  tests the source-level kernel semantics on the same GPU family, not the exact
  binary hash.

## Model side

`gemm_eval.lean` evaluates the same `gemmDot` (with `mem64` holding A at word 0
and B at word 4096) on the same inputs:

```
lake env lean Tools/conformance/gemm_eval.lean
```

Recorded output:

```
4294967294
4294967291
4
4294967290
```

The first three are the unsigned 32-bit forms of `C00`, `C11`, `C6363`
(`-2`, `-5`, `4`); the last is the checksum of all 4096 outputs. Both sides
agree bit-for-bit.

## Status

This is a conformance test, not a proof. The Lean side is the evaluated model;
the end-to-end theorem for this kernel is `IntelGpu.realGemm_output`.

# Hardware conformance: the real vector add

`vector_add.cpp` is the source used for the vector-add dump: `c[i] = a[i] + b[i]`
over 1024 `int`s, with `a[i] = i%7 - 3`, `b[i] = i%5 - 2`. Build and run with
oneAPI as above. Recorded result: `bad=0 sum=4294967289`.

# Hardware conformance: the straight-line vector add

`vector_add_nd.cpp` is the `nd_range<1>(1024, 64)` source whose dump is
`Intel/Examples/RealVectorAddFlat.lean`. Recorded run: `bad=0`.
