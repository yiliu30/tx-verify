# MUFU samples: exp, inv, log

Per-op error measurements for the three scalar math instructions used by the
FMHA prefill softmax/epilogue.

## Bench

`mufu_bench.cpp` runs three 2^20-point SYCL kernels on the lab GPU:

- `sycl::exp(x)` for `x` in `[-24, 0]`;
- `1.0f / x` for `x` in `(1/256, 1]`;
- `sycl::log(x)` for `x` in `[1e-6, 256]`.

Each result is compared with a double-precision host reference. Compiler:
oneAPI 2026.1 DPC++ with `-fsycl -O3`. An IGC dump of the same binary
contains `math.exp`, `math.inv` and `math.log`, so the measured kernels use
the instructions modelled in `Intel/TlaMath.lean`.

## Results (n = 1048576 per op)

| op | max abs error | max rel error |
| --- | --- | --- |
| exp | 1.170085644e-07 | 1.984444714e-07 |
| inv | 1.495941174e-05 | 1.153888151e-07 |
| log | 2.737414819e-07 | 7.661312768e-08 |

These exact values are recorded as `IntelGpu.labMufuSamples` in
`Intel/MufuSamples.lean` and can instantiate `MufuModel.expErr`/`invErr`/
`logErr`.

Product and host details are withheld per the project's policy.
