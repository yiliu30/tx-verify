# Hardware conformance: the SYCL-TLA 256x256x32 BF16 GEMM

This directory records a differential test between an actual Intel GPU run of
the SYCL-TLA BF16 GEMM (the kernel whose assembly is imported in
`Intel/Examples/RealTlaGemm.lean`) and a CUTLASS device reference GEMM.

## Kernel

The kernel is the unmodified SYCL-TLA example `00_bmg_gemm` built with oneAPI
2026.1 (`icpx -fsycl`). Its assembly dump is the `RealTlaGemm` input; the
sha256 provenance is recorded in `Intel/Examples/RealTlaGemm.lean`.

## Inputs

Both sides use the example's own initialization: the harness fills A, B and C
deterministically, runs the kernel into `D`, runs
`cutlass::reference::device::GemmComplex` into `ref_D`, and compares them
elementwise with `cutlass::reference::device::BlockCompareEqual` over all
65536 outputs.

## Hardware side

Run with oneAPI 2026.1.0:

```
source /opt/intel/oneapi/setvars.sh
./examples/00_bmg_gemm/00_bmg_gemm --m=256 --n=256 --k=32 --iterations=1 --verify=1
```

Recorded run:

```
Disposition: Passed
Problem Size: 256x256x32x1
Cutlass GEMM Performance:     [0.042]TFlop/s  (0.1008)ms
```

- compiler: Intel oneAPI DPC++/C++ 2026.1.0 (2026.1.0.20260617)
- device: an Intel discrete GPU; product and PCI details are withheld per the
  project's policy.

`Disposition: Passed` means the kernel's 256x256 output is bit-equal to the
reference GEMM on the same device for this problem size.

## Model side

The Lean model decodes the kernel's 2252 statements, executes the 32 DPAS
instructions as an ordered slab sum (`mainloopDpasRun_acc0_sum`,
`mainloopDpasRun_acc1_sum`) and proves that the accumulator stores write that
sum (`store21_dpas_sum`, `store25_dpas_sum`). The slab is an algebraic `Word`
model rather than a BF16 numeric model, so this run validates the hardware
kernel bit-exactly against a same-device reference; it does not compare
hardware numbers to the Lean slab values.
