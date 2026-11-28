# Intel GPU semantic core (stage 1)

Stage 1 of a staged Lean verification effort toward a SYCL-TLA GEMM kernel.

This stage adds a deliberately small Intel GPU / IGC semantic core and proves
the single-lane core of an `add_one` kernel. It is the foundation for the
later GEMM spec, IGC parser, and SYCL-TLA kernel proof.

## What is modeled

- Word-addressed global memory (one 32-bit word per address).
- 32-bit data registers and 64-bit address registers.
- `load.ugm.d32.a64`, `add`, `store.ugm.d32.a64`, and EOT.
- The modeled `d32` accesses assume 4-byte alignment.

## What is proved

`IntelGpu.core_correct`:

```lean
theorem core_correct (s : State) (addr : Addr) (v : Word)
    (h : AddOnePre s addr v) : AddOnePost s (run s core) addr v
```

For one lane: if the address register holds `addr` and the old word at that
address is `v`, the core sequence halts, writes `v + 1`, and leaves every
other word unchanged.

`#print axioms IntelGpu.core_correct` reports only `[propext, Quot.sound]`;
there is no `sorryAx` and no `bv_decide` certificate axiom.

## Stage 2: GEMM specification

`Intel/Gemm.lean` adds the exact integer GEMM loop invariant:

```lean
def dot (A B : Nat → Nat → Int) (i j : Nat) : Nat → Int
theorem gemmRun_acc ... : (gemmRun A B i j n).acc = dot A B i j n
def GemmSpec (A B C : Nat → Nat → Int) (M N K : Nat) : Prop
```

`#print axioms IntelGpu.gemmRun_acc` reports only `[propext]`. This is the
spec/loop layer; connecting it to the IGC loop body is stage 3.

## Not modeled yet

- IGC text parsing and register aliases (`r7:4`, `r12:2`).
- The compiler-generated prolog and global-id / address computation.
- SIMD masks, GRF regions, predicates, and scoreboards.
- SEND/EOT details beyond a halted flag.
- SLM, barriers, atomics, DPAS, and the launch ABI.

## Build

Lean 4.35.0:

```bash
lake build Intel
```

## Roadmap

1. Stage 1: minimal Intel GPU / IGC core and `add_one`.
2. Stage 2 (this PR): GEMM specification and loop invariant.
3. Stage 3: IGC text/parser and GEMM loop-body proof.
4. Stage 4: SYCL-TLA GEMM instance.
