-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.Syntax

@[expose] public section

/-!
# A real IGC kernel: SYCL add-one

Transcribed verbatim from the `_main_0` function that IGC emitted for

```cpp
q.parallel_for(sycl::range<1>(N), [=](sycl::id<1> i) { a[i] = a[i] + 1; });
```

Assembled body, in order (execution size is the first operand, as IGC prints
it):

```
or            (M1_NM, 1)  %cr0(0,0)<1>  %cr0(0,0)<0;1,0>  0x400004c0:ud
mul           (M1_NM, 1)  V0044(0,0)<1> V0038(0,0)<0;1,0> V0036(0,1)<0;1,0>
mov           (M1, 32)    V0045(0,0)<1> V0046(0,0)<1;1,0>
add3          (M1, 32)    V0047(0,0)<1> V0044(0,0)<0;1,0> V0045(0,0)<1;1,0> V0037(0,0)<0;1,0>
mov           (M1, 32)    V0048(0,0)<1> V0049(0,0)<1;1,0>
shl           (M1, 32)    V0051(0,0)<1> V0048(0,0)<1;1,0> 0x2:q
add           (M1, 32)    V0052(0,0)<1> V0051(0,0)<1;1,0> V0050(0,0)<0;1,0>
lsc_load.ugm  (M1, 32)    V0054:d32     flat[V0053]:a64
add           (M1, 32)    V0055(0,0)<1> V0054(0,0)<1;1,0> 0x1:w
lsc_store.ugm (M1, 32)    flat[V0053]:a64  V0055:d32
ret           (M1, 1)
```

## Provenance

- source: five-line SYCL program, `sycl::parallel_for` with `a[i] = a[i] + 1`
- compiler: oneAPI 2026.1 IGC, `zeinfo` format version `1.71`
- kernel attributes in the dump: `SimdSize=32`, `PerThreadInputSize=64`
- sha256 of the unredacted dump:
  `1a4889bedcfd0ac2152b57804fb6fc0a22723bb11c0ddca62848e1cbba4d035a`
- **redacted**: the dump's platform line and its build-option string, which name
  a product. Everything else is verbatim.

## What this is not

The operands keep IGC's region syntax (`(0,0)<1;1,0>`), register-file aliases
(`V0044` aliasing `%r0`), and typed suffixes (`:d32`, `:a64`). None of that is
decoded here; `Intel/RealCoverage.lean` measures exactly which instructions the
current decoder can and cannot read.
-/

namespace IntelGpu

/-- The real `add_one` kernel, transcribed. -/
def realAddOne : Program :=
  { statements := [
    .instruction "or"
      ["(M1_NM, 1)", "%cr0(0,0)<1>", "%cr0(0,0)<0;1,0>", "0x400004c0:ud"],
    .instruction "mul"
      ["(M1_NM, 1)", "V0044(0,0)<1>", "V0038(0,0)<0;1,0>", "V0036(0,1)<0;1,0>"],
    .instruction "mov" ["(M1, 32)", "V0045(0,0)<1>", "V0046(0,0)<1;1,0>"],
    .instruction "add3"
      ["(M1, 32)", "V0047(0,0)<1>", "V0044(0,0)<0;1,0>", "V0045(0,0)<1;1,0>",
       "V0037(0,0)<0;1,0>"],
    .instruction "mov" ["(M1, 32)", "V0048(0,0)<1>", "V0049(0,0)<1;1,0>"],
    .instruction "shl" ["(M1, 32)", "V0051(0,0)<1>", "V0048(0,0)<1;1,0>", "0x2:q"],
    .instruction "add"
      ["(M1, 32)", "V0052(0,0)<1>", "V0051(0,0)<1;1,0>", "V0050(0,0)<0;1,0>"],
    .instruction "lsc_load.ugm" ["(M1, 32)", "V0054:d32", "flat[V0053]:a64"],
    .instruction "add" ["(M1, 32)", "V0055(0,0)<1>", "V0054(0,0)<1;1,0>", "0x1:w"],
    .instruction "lsc_store.ugm" ["(M1, 32)", "flat[V0053]:a64", "V0055:d32"],
    .instruction "ret" ["(M1, 1)"],
  ] }

end IntelGpu
