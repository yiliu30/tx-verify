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
spec/loop layer.

## Stage 3: GEMM loop body

`Intel/GemmBody.lean` adds `mul`/`add` to the core and proves one straight-line
IGC-style body iteration:

```lean
theorem gemmBody_correct ... :
    let s' := run s gemmBody
    s'.regs 4 = sum + a * b ∧ s'.mem = s.mem ∧ s'.halted = s.halted
```

This is one lane; SIMD masks, loop control, pointer increment, and the
SYCL-TLA tile/DPAS kernel are later stages.

## Stage 4: IGC syntax/parser

`Intel/Syntax.lean` defines a raw IGC `Stmt`/`Program` syntax.
`Tools/parse_igc.py` parses a canonical GEMM loop-body fixture into
`Intel/Examples/GemmLoop.lean`, and `--check` verifies the generated file is
current. Operands remain raw strings; decoding is the next stage.

## Stage 16: SLM staging and workgroup barriers

`Intel/Slm.lean` adds a two-lane workgroup machine over word-indexed global
memory plus shared local memory:

```lean
structure WState where
  lanes : Nat → Lane   -- regs, global pointer, SLM pointer, done
  mem : Nat → Word
  slm : SLM
  phase : Nat
```

`barrier` retires only when no lane has finished early (`barrierOK`) and bumps
`phase`; a lane that already executed `eot` leaves the barrier stuck, which is
the modeled deadlock symptom for divergent exit.

`Intel/GemmSlm.lean` uses GEMM as the worked example. Lane 0 stages A row 0
into SLM words `[0, K)`, lane 1 stages A row 1 into `[K, 2K)`, the workgroup
hits a barrier, and the compute phase reads the staged tile:

```lean
theorem stageProg_correct ... : StageInv K K mem (wrun s (stageProg K))
theorem stageBarrier_correct ... :
    let s' := wrun s (stageProg K ++ [.barrier])
    s'.phase = 1 ∧ s'.mem = mem ∧ ...   -- staged tile readable by the group
theorem lane0_reads_lane1 ...           -- lane 0 reads lane 1's staged row
theorem gemmTile_slm_correct ... :
    ∀ l < 2, dotRange (fun t => s'.slm (l * K + t)) (fun t => B t 0) 0 K =
      dotMat A B l 0 K
```

`#print axioms` on each of these reports only `[propext, Quot.sound]`.

## Stage 17: workgroup control flow and the SLM compute loop

`Intel/WControl.lean` adds a pc-based program layer over the stage-16 machine:

```lean
inductive CInstr where
  | w (i : WInstr)
  | cmpGe (K : Nat)
  | incK
  | jmpiIf (target : Nat)
  | jmpi (target : Nat)
```

Control flow is uniform across the workgroup (one `pred`, one `k`), which is
the lockstep requirement a barrier already imposes; per-lane masks are a later
refinement.

`Intel/GemmSlmCompute.lean` runs the compute phase for real. `computeProg K`
loads A from the lane's SLM slot, loads the B column from global memory,
multiplies, accumulates into register 4, advances both pointers and the shared
counter, and branches while `k < K`:

```lean
theorem dotRange_add_last ...        -- loop appends one term per iteration
theorem dotRange_eq_dotMatFrom ...   -- loop sum agrees with the spec
theorem computeProg_correct ... :
    let s' := crun (computeProg K) (10 * K + 3) s
    s'.halted = true ∧ s'.w.phase = 1 ∧
      ∀ l < 2, (s'.w.lanes l).regs 4 = dotMat A B l 0 K
theorem gemmTile_executed ... :      -- staging + barrier + loop, end to end
    fin.halted = true ∧ fin.w.phase = 1 ∧
      ∀ l < 2, (fin.w.lanes l).regs 4 = dotMat A B l 0 K
```

`#print axioms` on each of these reports only `[propext, Quot.sound]`.

## Stage 18: DPAS / XMX tiled accumulation

`Intel/Dpas.lean` models the XMX systolic instruction. One `dpas` updates a
whole output tile:

```
C[m][n] += Σ_{k < d} A[k][m] * B[k][n]
```

with systolic depth `d` (`systolicDepth = 8` on Xe-HPC). A GEMM tile of depth
`K` is `T = K / d` instructions, each fed the next depth slab:

```lean
def dpasSlab ...                    -- systolic dot over one slab
def dpas (d) (A B) (C) ...          -- one instruction
def dpasRun ... (T) (C) ...         -- T back-to-back instructions
theorem dotMatFrom_append ...       -- split the spec at a depth boundary
theorem dpasSlab_eq_dotMatFrom ...  -- one slab is a slice of the spec
theorem dpasRun_correct ... :
    dpasRun A B i j d T (fun _ _ => 0) m n = dotMat A B (i + m) (j + n) (T * d)
theorem dpasRun_systolic ...        -- the depth-8 specialization
```

`Intel/GemmDpasLoop.lean` makes it executable. `dpasProg T` is the mainloop
(`cmpGe`, `jmpiIf`, load A slab, load B slab, `dpas`, `incT`, `jmpi`), and

```lean
theorem dpasProg_correct ... :
    let s' := xrun ... (dpasProg T) (7 * T + 3) s
    s'.halted = true ∧
      ∀ m n, s'.acc m n = dotMat Ag Bg (i + m) (j + n) (T * d)
```

The depth remainder (`K` not a multiple of `d`) is handled at the kernel
instance stage, where the last slab is masked.

`#print axioms` on each of these reports only `[propext, Quot.sound]`.

## Not modeled yet

- IGC text parsing and register aliases (`r7:4`, `r12:2`).
- The compiler-generated prolog and global-id / address computation.
- SIMD masks, GRF regions, predicates, and scoreboards.
- SEND/EOT details beyond a halted flag.
- SLM bank layout and conflicts, sub-group masks, and barrier scheduling.
- Atomics, DPAS, and the launch ABI.

## Build

Lean 4.35.0:

```bash
lake build Intel
```

## Roadmap

1. Stage 1: minimal Intel GPU / IGC core and `add_one`.
2. Stage 2: GEMM specification and loop invariant.
3. Stage 3: GEMM loop-body semantics.
4. Stage 4: IGC syntax and parser.
5. Stage 5: typed IGC operand decoding.
6. Stage 6: IGC loop-control step semantics.
7. Stage 7: data + control-flow semantics.
8. Stage 8: GEMM body through data/control.
9. Stage 9: dot-product loop invariant.
10. Stage 10: memory body with pointer advance.
11. Stage 11: word-indexed memory GEMM loop.
12. Stage 12: matrix GEMM specification.
13. Stage 13: GEMM tiling and tile coverage.
14. Stage 14: tile scheduler enumeration.
15. Stage 15: scheduled-tile correctness and global composition.
16. Stage 16: SLM staging and workgroup barriers.
17. Stage 17: workgroup control flow and the SLM GEMM compute loop.
18. Stage 18 (this PR): DPAS/XMX tiled accumulation and its executed mainloop.
19. Stage 19: the SYCL-TLA GEMM instance (source manifest, spec, and
    refinement statement).
