# Intel GPU semantic core

A staged Lean verification effort toward a SYCL-TLA GEMM kernel. Stage 1 built
the ISA core; later stages add the GEMM spec, the IGC parser, tiling, SLM,
DPAS, the SYCL-TLA instance, the numeric layer and the fp16 encoding. The
roadmap at the end lists all 54 stages.

## Audited headline theorems

`python3 Tools/check_axioms.py --md` regenerates this table. It is a curated
subset — one headline per layer — not every stage, and the numbers are table
entries, not stage numbers. The full sweep is `--all`.

| # | Module | Headline theorem | Axioms |
|---|---|---|---|
| 1 | `Intel.AddOne` | `core_correct` | Quot.sound, propext |
| 2 | `Intel.Gemm` | `gemmRun_acc` | propext |
| 3 | `Intel.GemmBody` | `gemmBody_correct` | Quot.sound, propext |
| 4 | `Intel.Examples.GemmLoopDecoded` | `decode_gemmLoop` | Classical.choice |
| 5 | `Intel.GemmControl` | `gemmBodyD_correct` | Quot.sound, propext |
| 6 | `Intel.GemmLoop` | `dotProgram_correct` | Quot.sound, propext |
| 7 | `Intel.Address` | `gemmMemoryBody_correct` | Quot.sound, propext |
| 8 | `Intel.GemmMemoryLoop` | `mProgram_correct` | Quot.sound, propext |
| 9 | `Intel.GemmMatrix` | `mProgram_matrix` | Quot.sound, propext |
| 10 | `Intel.GemmTiling` | `gemmSpecW_of_tiles` | Quot.sound, propext |
| 11 | `Intel.GemmScheduler` | `mem_tileSchedule_of_lt` | Quot.sound, propext |
| 12 | `Intel.GemmScheduleProof` | `gemmSpecW_of_schedule` | Quot.sound, propext |
| 13 | `Intel.GemmSlm` | `gemmTile_slm_correct` | Quot.sound, propext |
| 14 | `Intel.GemmSlmCompute` | `gemmTile_executed` | Quot.sound, propext |
| 15 | `Intel.Dpas` | `dpasRun_correct` | Quot.sound, propext |
| 16 | `Intel.GemmDpasLoop` | `dpasProg_correct` | Quot.sound, propext |
| 17 | `Intel.TlaInstance` | `tlaXeF16_gemm_spec` | Quot.sound, propext |
| 18 | `Intel.DpasAtom` | `dpasSlab_two_atoms` | Quot.sound, propext |
| 19 | `Intel.DpasMask` | `tlaXeF16_gemm_spec_tail` | Quot.sound, propext |
| 20 | `Intel.Epilogue` | `gemmTile_end_to_end` | Quot.sound, propext |
| 21 | `Intel.EpilogueLd` | `epilogueLd_correct` | Quot.sound, propext |
| 22 | `Intel.EpilogueFrame` | `epilogueLd_frame` | Quot.sound, propext |
| 23 | `Intel.SharedBuffer` | `writeTiles_frame` | Quot.sound, propext |
| 24 | `Intel.SharedBuffer` | `separated_of_width` | Quot.sound, propext |
| 25 | `Intel.SharedBuffer` | `writeTiles_block` | Quot.sound, propext |
| 26 | `Intel.GemmAssembly` | `tlaXeF16_gemm_executed` | Quot.sound, propext |
| 27 | `Intel.Staging` | `stageSlab_correct` | Quot.sound, propext |
| 28 | `Intel.Mainloop` | `mainloop_correct` | Quot.sound, propext |
| 29 | `Intel.LaneStaging` | `laneBlock_value` | Quot.sound, propext |
| 30 | `Intel.Interleaved` | `copyInterleaved_value` | Quot.sound, propext |
| 31 | `Intel.InterleavedLanes` | `lane_mod` | Quot.sound, propext |
| 32 | `Intel.TilePipeline` | `mainloop_epilogue` | Quot.sound, propext |
| 33 | `Intel.Numeric` | `maccDot_error` | Quot.sound, propext |
| 34 | `Intel.Rounding` | `truncDot_error` | Quot.sound, propext |
| 35 | `Intel.RoundingNearest` | `roundDot_error` | Quot.sound, propext |
| 36 | `Intel.RoundingEven` | `evenDot_error` | Quot.sound, propext |
| 37 | `Intel.NumericBridge` | `wpDot_error` | Quot.sound, propext |
| 38 | `Intel.Exactness` | `evenDot_exact_on_grid` | Quot.sound, propext |
| 39 | `Intel.Fp16Shape` | `fp16_grid_exact_of_exp` | Quot.sound, propext |
| 40 | `Intel.Fp16Bits` | `fp16_bits_exact` | Quot.sound, propext |
| 41 | `Intel.Fp16Value` | `foldVal_fin` | propext |
| 42 | `Intel.Fp16Scaled` | `scaled_normal` | Quot.sound, propext |

## Assumption ledger

Every claim in this file is relative to these assumptions. Each is stated in
code and, where possible, exercised by an executable check; nothing here rests
on a silent assumption.

1. **Memory model** — word-addressed, modelled `d32` accesses 4-byte aligned.
   `Intel/Asm.lean` states the abstraction and takes alignment as an explicit
   precondition; stage 60 collects the store/load laws every frame argument
   needs (`Intel/MemoryLaws.lean`). Discharged in part — byte-level addressing
   and endianness are not modelled.
2. **Lane dimension** — the machines are scalar. Stage 59 adds a SIMD layer
   (`Intel/Simd.lean`): per-lane scalar states plus a mask, with predication
   (`simdRun`), and `add_one_simd` lifting the stage-1 proof to every active
   lane. Discharged in part — GRF regions and sub-group packing are not
   modelled.
3. **Uniform control flow** — `Intel/WControl.lean` gets it for free via a
   single predicate. Stage 58 states what it buys (`Intel/Divergence.lean`): a
   barrier retires only when every lane has parked, so one diverged lane leaves
   the workgroup stuck. Discharged in part — the hazard is proved, the masks
   themselves are not modelled.
4. **SLM visibility** — `Intel/Slm.lean` makes writes visible at retire, so the
   barrier only orders phases there. Stage 55 adds the minimal hazard model
   (`Intel/SlmLatency.lean`) and proves the barrier is *necessary*: reading
   before it sees stale data. Discharged in part — write latency is a single
   pending buffer, not a pipeline.
5. **DPAS as a tile operation** — `Intel/Dpas.lean`. Discharged in part by
   stage 49: a depth-`d` slab is a chain of atom-depth instructions over
   shifted operands (`dpasSlab_split`, `dpasSlab_two_atoms`), so the tile
   operation is a composition rather than a primitive. Register-file dispatch
   itself is still not modelled.
6. **Tile shape** `256 x 256 x 32` with an `8 x 16 x 16` atom, taken from the
   upstream Xe GEMM configuration. `Intel/TlaInstance.lean`. Re-check if
   upstream changes.
7. **Accumulator rounding** — nearest, ties to even, on the accumulator
   quantum. `Intel/NumericBridge.lean` (`hstep`). Discharged on a shared grid
   (stage 34); bounded by `n * (q / 2)` off it (stages 30-32).
8. **Staging** — **discharged in both shapes**. Block distribution: stage 37.
   Interleaved: `copyInterleaved` (stage 50), residue-class disjointness
   (stage 51), and full slab coverage `lanesInterleaved_covers` (stage 57).
9. **fp16 classes** — **discharged**. NaN carries a payload with a stated
   propagation rule (`Fp16Value.lean`, stage 61); infinities carry a sign and
   follow the same-sign/opposite-sign rule (stage 44); subnormals are values in
   units of `2 ^ -24` (stage 46) tied to the numeric scale (stage 56).

Assumption 7 is the one with real numeric content, and it is the one that has
been reduced furthest: on a shared quantization grid the rounding is the
identity (stage 34), so exactness holds outright; off the grid the error is
bounded by `n * (q / 2)` (stages 30-32).

`python3 Tools/check_axioms.py --all` audits **every** theorem in every Intel
module — 200 of them — and `.github/workflows/build.yml` runs that on every push
and pull request. The curated default (one headline per stage) is the quick
check; `--all` is the gate.

## What is modeled (stage 1)

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

## Stage 19: SYCL-TLA Xe GEMM instance

`Intel/TlaInstance.lean` pins the shape of the Xe DPAS GEMM in SYCL-TLA,
taken from `test/unit/gemm/device/default_gemm_configuration.hpp`:

```
using TileShape = Shape<_256, _256, _32>;
using TiledMma  = TiledMMAHelper<MMA_Atom<XE_8x16x16_F32F16F16F32_TT>, ...>::TiledMMA;
```

so a workgroup tile is `256 x 256` with K tile `32`, and an atom is `8 x 16`
with depth `16` (two atoms deep per K tile).

```lean
def tlaXeF16 : TlaShape          -- 256 x 256 x 32, atom 8 x 16 x 16
theorem tlaXeF16_mAtoms ...      -- 256 = 32 * 8
theorem tlaXeF16_nAtoms ...      -- 256 = 16 * 16
theorem tlaXeF16_kAtoms ...      -- 32 = 2 * 16
theorem tlaXeF16_dpasPerTile ... -- 1024 DPAS instructions per workgroup tile
theorem tlaXeF16_kTile_mainloop ... -- one K tile executes in 17 steps
```

The refinement statement composes stages 15 and 18:

```lean
theorem tileSpec_of_dpas ... :    -- DPAS-produced tile satisfies TileSpec
theorem tla_gemm_spec ... : GemmSpecW A B C M N K
theorem tlaXeF16_gemm_spec ... : -- the 256x256x32 instance
```

Assumptions are stated in the module doc: K a multiple of the atom depth (no
last-slab masking), operands already in the DPAS tile registers, and elements
modeled as 32-bit words so fp16/bf16 rounding is out of scope.

`#print axioms` on each reports only `[propext, Quot.sound]`.

## Stage 20: partial K tail

`Intel/DpasMask.lean` removes the "K is a multiple of the atom depth"
assumption. The last K tile has only `r` live depth slots, which on Xe is the
same instruction with the remaining slots masked, i.e. a `dpas` of live depth
`r`:

```lean
def dpasTail ...                    -- T full slabs plus one r-deep slab
theorem dpasTail_correct ... :
    dpasTail A B i j d T r (fun _ _ => 0) m n = dotMat A B (i + m) (j + n) (T * d + r)
theorem tileSpec_of_dpasTail ...    -- TileSpec for K = T * d + r
theorem tla_gemm_spec_tail ... : GemmSpecW A B C M N K
theorem tlaXeF16_gemm_spec_tail ... -- every K: K / 16 full slabs, K % 16 tail
```

`#print axioms` on each reports only `[propext, Quot.sound]`.

## Stage 21: executed epilogue store

`Intel/Epilogue.lean` closes the last executable gap for one tile: the
accumulator is written to global memory by a real loop rather than assumed to
appear in C.

```lean
def epilogueProg (T : Nat)          -- cmpGe / jmpiIf / store / inc / jmpi
theorem epilogue_correct ... :
    let s' := erun base N (epilogueProg T) (5 * T + 3) (eHead mem acc)
    s'.halted = true ∧ ∀ k < T, s'.mem (base + k) = acc (k / N) (k % N)
theorem epilogue_block ...          -- the tile lands at its C block, origin (gi, gj)
theorem gemmTile_end_to_end ... :   -- DPAS mainloop + epilogue, end to end
    s1.halted = true ∧ e.halted = true ∧
      ∀ m < BM, ∀ n < BN,
        e.mem (base + (ti * BM + m) * BN + (tj * BN + n)) =
          dotMat A B (ti * BM + m) (tj * BN + n) (T * d)
theorem tileSpec_of_store ...       -- bridges the store to TileSpec
```

`#print axioms` on each reports only `[propext, Quot.sound]`.

## Stage 22: epilogue with a leading dimension

`Intel/EpilogueLd.lean` generalizes the stage-21 store from a packed tile to a
row-major output with leading dimension `ldC ≥ N`.

The only new ingredient is that strided tile indices must not alias:

```lean
theorem packed_inj ...               -- k ↦ (k / N) * ldC + k % N is injective
theorem epilogueLd_correct ... :
    let s' := lrun base ldC N (epilogueProg (M * N)) (5 * (M * N) + 3) (eHead mem acc)
    s'.halted = true ∧ ∀ m < M, ∀ n < N, s'.mem (base + m * ldC + n) = acc m n
```

`#print axioms` on each reports only `[propext, Quot.sound]`.

## Stage 23: assembling the tiles

`Intel/GemmAssembly.lean` puts the tiles back together.

- `gemmTile_end_to_end_ld`: one tile's DPAS mainloop plus strided epilogue
  leaves `dotMat` in memory at the tile's block.
- `gemmSpecW_of_tilesExecuted`: if every scheduled tile's block holds `dotMat`,
  the stitched matrix `fun x y => memOf (x / BM) (y / BN) (base + x * ldC + y)`
  satisfies `GemmSpecW`. Each element is read from the memory of its owning
  tile, which the stage-15 scheduler shows exists.
- `tlaXeF16_gemm_executed`: the same statement at the SYCL-TLA `256 x 256`
  workgroup shape.

`#print axioms` on each reports only `[propext, Quot.sound]`.

## Stage 24: operand staging into SLM

`Intel/Staging.lean` produces the DPAS operands instead of assuming them. A
bulk copy moves an `M x d` A slab and an `N x d` B slab from global memory into
SLM in the row-major layout the operands need, then a barrier retires:

```lean
def copyN ...                       -- dstMem[dst + k] := srcMem[src + k]
theorem copyN_value ...             -- every copied word lands
theorem copyN_frame ...             -- words outside the range are untouched
def stageSlabProg ...               -- copy A, copy B, barrier
theorem stageSlab_correct ... :
    s.phase = 1 ∧
      (∀ k < d, ∀ m < M, s.slm (m * d + k) = mem (aBase + m * d + k)) ∧
      (∀ k < d, ∀ n < N, s.slm (M * d + n * d + k) = mem (bBase + n * d + k))
theorem dpas_from_staged ...        -- the staged tile is the DPAS operand slab
```

`#print axioms` on each reports only `[propext, Quot.sound]`.

## Stage 25: the composed mainloop

`Intel/Mainloop.lean` runs staging and DPAS as one loop, which is the shape of
the SYCL-TLA mainloop:

```
for t in 0 .. T:
  stage A slab t   (strided copy, global -> SLM)
  stage B slab t   (strided copy, global -> SLM)
  barrier
  dpas             (accumulate the slab into the C tile)
```

- `copyStrided` / `copyStrided_value` / `copyStrided_frame`: strided copies with
  the value and frame laws.
- `dpasSlab_congr`: the slab only reads its own operand row/column, so
  pointwise agreement on depth slots is enough.
- `staged_A` / `staged_B`: after staging, the SLM tiles are exactly the A and B
  slabs at the right offsets.
- `mainloop_correct`: `8 * T + 3` steps halt with `phase = T` and
  `acc = dotMat` at depth `T * d`.

`#print axioms` on each reports only `[propext, Quot.sound]`.

## Stage 26: one tile, fully executed

`Intel/TilePipeline.lean` runs the stage-25 mainloop and the stage-22 epilogue
back to back, so a single output tile goes from global memory to its C block in
one executed pipeline.

- `mainloop_epilogue`: `T` staged slabs, `T` barriers, `T` DPAS steps, then the
  strided epilogue — halting with `dotMat` in the tile's C block.
- `tileSpec_of_mainloop`: the same fact as `TileSpec`, so the stage-15/23
  assembly applies to the executed pipeline.

`#print axioms` on `mainloop_epilogue` reports only `[propext, Quot.sound]`;
`tileSpec_of_mainloop` uses no axioms.

## Stage 27: rounding contract and accumulation error

Everything through stage 26 is exact integer arithmetic, which is the wrong
shape for a real fp16/bf16 kernel. `Intel/Numeric.lean` supplies the standard
shape: a per-step contract plus an accumulation bound.

```lean
def accDot ...                      -- exact, depth-ordered accumulation
def maccDot ...                     -- the same accumulation on the machine
theorem maccDot_error ... :         -- n steps are within n * eps
    (maccDot step a b acc n - accDot a b acc n).natAbs ≤ n * eps
theorem maccDot_zero_error ...      -- no rounding error ⇒ exact result
theorem dpas_chain_error ... :      -- T slabs of depth d: error ≤ T * d * eps
    ... ≤ T * d * eps
def toInt (w : Word) : Int          -- signed reading of a 32-bit word
```

The bound grows with accumulation depth `T * d`, not with the number of tiles,
which is why a kernel splits K into slabs without changing the error class.

The contract

```lean
hstep : ∀ c x y, (step c x y - (c + x * y)).natAbs ≤ eps
```

is the hardware assumption: it says each machine multiply-add is within `eps`
units of the exact one. Deriving it needs bit-level fp16/fp32 semantics, which
is a separate development; stating it keeps the accumulation argument honest
and reusable.

`#print axioms` on these reports only `[propext, Quot.sound]` (`maccDot_zero_error`
uses no axioms).

## Stage 28: executed tail slab

The stage-25 mainloop needs `K = T * d`. `Intel/MainloopTail.lean` adds the
partial last slab, so the executed pipeline covers every depth `K`:

```lean
def tailProg (t r : Nat)          -- stage A tail, stage B tail, barrier, depth-r DPAS
theorem stagedTail_A ...          -- SLM holds A[i + m][t*d + k] in the tail layout
theorem stagedTail_B ...
theorem tail_correct ...          -- depth-r tail on top of a depth-t*d accumulator
theorem mainloop_tail_correct ... :
    T full slabs then a depth-r tail give dotMat at depth T * d + r
```

The tail keeps its own SLM layout (`m * r + k`, `M * r + k * N + n`), which is
the layout a depth-`r` DPAS reads.

`#print axioms` on each reports only `[propext, Quot.sound]`.

## Stage 29: a concrete rounding and its derived contract

Stage 27 takes the per-step error `eps` as a hypothesis. `Intel/Rounding.lean`
supplies a concrete rounding and derives it.

```lean
def truncQ (q : Nat) (x : Int) : Int      -- truncate toward zero to a multiple of q
theorem truncQ_bound ... :                -- error strictly below q
    (truncQ q x - x).natAbs < q
theorem truncQ_one (z : Int) : truncQ 1 z = z
def stepTrunc (q : Nat) ...               -- machine multiply-add with truncation
theorem stepTrunc_contract ... :          -- meets the stage-27 contract, eps = q - 1
    (stepTrunc q c x y - (c + x * y)).natAbs ≤ q - 1
theorem truncDot_error ... :              -- accumulated bound
    ... ≤ n * (q - 1)
theorem truncDot_exact ...                -- q = 1 ⇒ exact
```

`#eval truncQ 8 37` is `32` and `#eval truncQ 8 (-37)` is `-32`, as a
toward-zero truncation should be.

The remaining assumption is now "the hardware truncates to the accumulator
quantum" instead of an abstract error bound. IEEE-754 subnormals, ties-to-even
and fp16 exponent range are still out of scope.

`#print axioms` on each reports only `[propext, Quot.sound]`.

## Stage 30: round to nearest

`Intel/RoundingNearest.lean` halves the stage-29 bound by rounding instead of
truncating.

```lean
def roundQ (q : Nat) (x : Int) : Int     -- nearest multiple of q, ties toward zero
theorem roundQ_bound ... :               -- error at most q / 2
    (roundQ q x - x).natAbs ≤ q / 2
theorem roundQ_one (z : Int) : roundQ 1 z = z
def stepRound (q : Nat) ...              -- machine multiply-add with nearest rounding
theorem stepRound_contract ...           -- stage-27 contract with eps = q / 2
theorem roundDot_error ... :             -- n steps within n * (q / 2)
    ... ≤ n * (q / 2)
theorem roundDot_exact ...               -- q = 1 ⇒ exact
```

`#eval roundQ 8 36` is `40`, `#eval roundQ 8 33` is `32`, `#eval roundQ 8 35`
is `32` — a tie resolves toward zero, which the module documents. Real
hardware resolves ties to even; that is a refinement of the same bound
argument, not a different one.

`#print axioms` on each reports only `[propext, Quot.sound]`.

## Stage 31: ties to even

`Intel/RoundingEven.lean` models the tie rule hardware actually uses.

```lean
def roundEvenNat (q n : Nat) : Nat   -- ties go to the multiple with even quotient
def roundEven (q : Nat) (x : Int) : Int
theorem roundEven_bound ... :        -- error at most q / 2
    (roundEven q x - x).natAbs ≤ q / 2
def stepEven (q : Nat) ...           -- machine multiply-add with ties-to-even
theorem stepEven_contract ...        -- stage-27 contract with eps = q / 2
theorem evenDot_error ... :          -- n steps within n * (q / 2)
    ... ≤ n * (q / 2)
example : roundEven 8 35 = 32        -- tie: quotient 4 is even
example : roundEven 8 45 = 48        -- tie: quotient 5 is odd
```

The bound is unchanged from stage 30 — the tie rule only changes *which* of the
two equidistant multiples is chosen — so the numeric theorems carry over
untouched.

`#print axioms` on `roundEven_bound` and `evenDot_error` reports only
`[propext, Quot.sound]`; the branch lemmas use no axioms at all.

## Stage 32: from word arithmetic to the numeric bound

Stages 27-31 bound an accumulation over `Int`; the machines compute over
`Word`. `Intel/NumericBridge.lean` connects them.

```lean
def wpDot ...                        -- depth-ordered accumulation over Word
theorem wpDot_toInt ... :            -- equality: the reading of the word run is
    toInt (wpDot step a b acc n) =   --   the stage-31 machine accumulation
      maccDot (stepEven q) ... n
theorem wpDot_error ... :            -- error at most n * (q / 2)
    ... ≤ n * (q / 2)
theorem dpasWord_error ... :         -- T slabs of depth d: T * d * (q / 2)
    ... ≤ T * d * (q / 2)
```

`wpDot_toInt` is an equality, not a bound: if the word step implements
ties-to-even rounding on the signed reading (`hstep`), the word accumulation
*is* the machine accumulation of stage 31, and the error bound follows. The
single hypothesis left is the fp32 accumulator contract, stated explicitly.

`#print axioms`: `wpDot_toInt` uses none; `wpDot_error` and `dpasWord_error`
use only `[propext, Quot.sound]`.

## Stage 33: executable smoke tests

Everything here is a `def`, so the machines run. `Intel/Smoke.lean` executes
the real definitions on tiny inputs and checks the arithmetic in the kernel
(`decide`, not `native_decide` — the repo forbids the latter):

```lean
example : (krun smokeGeom (mainloopProg 2) 19 (kHead smokeMem ...)).acc 0 0 = 39
example : (krun smokeGeom (tailProg 1 1) 4 ...).acc 0 0 = 39          -- full slab + tail
example : (lrun 0 1 1 (epilogueProg 1) 8 (eHead ...)).mem 0 = 39      -- epilogue store
example : truncQ 8 37 = 32
example : roundQ 8 37 = 40
example : roundEven 8 35 = 32                                          -- tie to even
```

with `A = [3, 4]`, `B = [5, 6]`, so the expected result is `3*5 + 4*6 = 39`.
These are evidence the model is not vacuous: staging, barrier, DPAS, the tail
path, the epilogue and the roundings all compute what the theorems say.

## Stage 34: exactness on a shared grid

The numeric layer bounds the error of a rounded accumulation. This stage gives
the case where there is no error: if the operands and the accumulator all sit
on the same quantum grid — the shared-exponent-window case — every product and
partial sum is exactly representable, so rounding is the identity.

```lean
theorem roundEvenNat_mul ...         -- rounding a multiple of q changes nothing
theorem roundEven_fixed ...          -- signed version, k * q
theorem stepEven_grid ...            -- a multiply-add of grid values is exact
theorem evenDot_exact_on_grid ... :  -- so is an n-deep accumulation
    maccDot (stepEven q) ... n = accDot ... n
```

This is the bridge back to stages 1-28: on the grid the machine accumulation
equals the exact integer dot, so the exact-integer theorems apply verbatim to
that input class. Off the grid, stage 31/32 bound the error by `n * (q / 2)`.

`#print axioms` on each reports only `[propext, Quot.sound]`.

## Stage 35: executable checks for the workgroup stages

`Intel/SmokeSlm.lean` extends the smoke tests to the stage-16/17 machines:
two-lane SLM staging, the barrier, and the SLM compute loop, on the same tiny
GEMM.

```lean
example : (wrun smokeW (stageProg 2 ++ [.barrier])).slm 0 = 3   -- staging
example : (wrun smokeW (stageProg 2 ++ [.barrier])).phase = 1   -- barrier retired
example : (... computeProg 2 ...).w.lanes 0).regs 4 = 88        -- 3*12 + 4*13
example : (... computeProg 2 ...).w.lanes 1).regs 4 = 138       -- 5*12 + 6*13
example : (... computeProg 2 ...).halted = true
```

Lane 1 computing `138` rather than `88` is the model behaving correctly: each
lane reads its own staged row. I got that wrong when writing the test and
`#eval` corrected me, which is the point of having executable checks.

## Stage 36: an axiom audit over the whole stack

Every stage advertises an axiom footprint. `Tools/check_axioms.py` checks that
claim mechanically over one headline theorem per stage:

```bash
python3 Tools/check_axioms.py
# OK: 30 theorems, 1 documented exception(s), axioms within {Quot.sound, propext}
```

It writes a temporary Lean file per theorem and parses `#print axioms`, so a
regression shows up as a build-time failure rather than a stale claim. One
Lean run per theorem is deliberate: `Intel.GemmLoop` and
`Intel.GemmMemoryLoop` both define `dotRange`, so importing them into one
environment fails.

The audit found a real dependency the README had not recorded:
`IntelGpu.decode_gemmLoop` (stage 5) uses `Classical.choice`. The cause is
`String.toList` in Lean's core library, which is itself proved with
`Classical.choice`; nothing in the decoder reasons classically. It is listed as
a documented exception with that reason rather than silently allowed.

## Stage 37: distributed staging across lanes

`Intel/LaneStaging.lean` gives the workgroup copy a per-lane reading: lane `l`
moves the `c` words at `slm[dst + l * c]`, and the workgroup copy is the fold
over lanes.

The fold nests copies inside-out — lane 0 first, lane `l` last — which is
exactly `copyStrided` with row stride and row length `c`:

```lean
def laneBlockFold ...
theorem laneBlockFold_eq_copyStrided ...   -- no axioms: definitional
theorem laneBlock_value ...                -- lane j's word i comes from the same offset
theorem laneBlock_frame ...                -- nothing outside the slab moves
theorem laneBlock_disjoint ...             -- an earlier lane's chunk is never clobbered
```

So stage 25's value and frame laws carry over verbatim, and the "one bulk
copy" of stages 24/25 is now also a distribution with stated ownership. A fold
that applied lane `l` first would write the same memory but would not line up
with the strided copy's recursion — that ordering is what makes the
identification definitional, and it is noted in the module.

`#print axioms`: `laneBlockFold_eq_copyStrided` uses none; the rest only
`[propext, Quot.sound]`.

## Stage 38: fp16-shaped values on a shared grid

Stage 34 takes the shared grid as a hypothesis. `Intel/Fp16Shape.lean` supplies
it from an fp16-shaped value: `sign * mantissa * 2 ^ exponent` with an 11-bit
significand.

```lean
structure Fixed where           -- sign, mantissa, unbiased exponent
  sign : Bool
  mant : Nat
  exp : Nat
def Fixed.mag ...               -- mantissa * 2 ^ exponent
theorem Fixed.mag_eq ... :      -- an exponent >= e0 means a multiple of 2 ^ e0
    v.mag = v.mant * 2 ^ (v.exp - e0) * 2 ^ e0
theorem fp16_grid_exact ...     -- grid values accumulate exactly (stage 34)
theorem fp16_grid_exact_of_exp ... :
    -- every exponent >= e0 ⇒ maccDot (stepEven (2 ^ e0)) ... = accDot ...
    ... = accDot ...
```

So fp16 operands whose exponents share a floor `e0`, accumulated on the same
grid, compute the exact integer dot product with no rounding at all — the
stage-34 hypothesis is now derived, not assumed.

Out of scope, and said so in the module: negative exponents (subnormals and
fractional values), NaN/Inf, and exponent overflow.

`#print axioms` on each reports only `[propext, Quot.sound]`.

## Stage 39: the epilogue is a frame-preserving write

Stage 22 proves what the epilogue writes; `Intel/EpilogueFrame.lean` proves what
it does not touch. That is what a shared output buffer needs — writing tile
after tile into one `C` cannot disturb a tile already written.

```lean
structure LInvF ...              -- the stage-22 invariant plus a frame field
theorem lstep_iter_frame ...     -- one iteration keeps the block and the frame
theorem epilogueLd_frame ... :
    -- a outside the M x N block ⇒ the epilogue leaves mem a alone
    ... .mem a = mem a
```

`#print axioms` on each reports only `[propext, Quot.sound]`.

## Stage 40: one output buffer for all tiles

`Intel/SharedBuffer.lean` starts the shared-buffer story now that the epilogue
has a frame law.

```lean
def sliceAddr ...        -- address of element (m, n) of tile p's block
def tileEpilogue ...     -- run tile p's epilogue on a memory
def writeTiles ...       -- fold the per-tile epilogues over a list of origins
def Separated ...        -- different origins never share a block address
theorem writeTiles_frame ... :
    -- a word outside every block is left alone by the whole fold
    ... a = mem a
```

So writing tiles in sequence cannot disturb any word outside their blocks. Two
things are deliberately **not** claimed yet, and the module says so: that
`Separated` follows from the tile arithmetic (it needs the matrix width,
`p.2 * BN + BN ≤ N ≤ ldC`), and that a word *inside* a block ends up holding
that tile's accumulator. Those are the remaining half.

`#print axioms` on each reports only `[propext, Quot.sound]`.

## Stage 41: blocks are separated

Stage 40 left `Separated` as a hypothesis. This stage derives it.

```lean
theorem mul_add_inj ...          -- BM-ary carries are injective below BM
theorem addr_inj ...             -- row-major addresses injective when the column fits ldC
theorem separated_of_width ... :
    -- N ≤ ldC, and every origin's block fits N  ⇒  Separated base ldC BM BN origins
    Separated base ldC BM BN origins
```

Two different tile origins therefore never share a buffer address, given the
usual `N ≤ ldC` and that each tile block lies inside the matrix width. The
address arithmetic is the part stage 40 could not do with `BN ≤ ldC` alone:
global columns reach `p.2 * BN + n`, so the bound has to be the matrix width,
not the tile width.

Stage 42 finishes the story: `writeTiles_block` shows that a word *inside* a
block ends up holding that tile's accumulator, given separated blocks and
distinct origins.

`#print axioms` on each reports only `[propext, Quot.sound]`.

## Stage 42: the shared buffer is complete

`writeTiles_block` closes the other half:

```lean
theorem writeTiles_block ... :
    -- separated blocks, distinct origins, p in the list
    writeTiles ... origins mem (sliceAddr ... p m n) = acc p.1 p.2 m n
```

Together with `writeTiles_frame`, writing the tiles in sequence into one `C`
gives every tile its own block and disturbs nothing outside the blocks — the
stage-23 functional stitching is now a special case rather than the only
option.

The proof is an induction on the origin list. For the head tile it uses the
epilogue's own correctness for its block and the frame law for the rest; for a
tile in the tail it uses the induction hypothesis directly, because the
separation law says the head cannot touch it.

`#print axioms` on each reports only `[propext, Quot.sound]`.

## Stage 43: a bit-level fp16 encoding

Stage 38 models `sign * mantissa * 2 ^ exponent` and takes the shape on faith.
`Intel/Fp16Bits.lean` grounds it in the 16-bit layout: sign bit, 5-bit biased
exponent, 10-bit mantissa.

```lean
abbrev Fp16 := BitVec 16
def signBit / expField / mantField ...   -- the three fields
def decode (w : Fp16) : Option Fixed     -- none for the out-of-scope classes
theorem decode_some ...                  -- a successful decode pins the fields
theorem decode_exp_ne ...                -- a decoded word is never NaN/Inf
theorem fp16_bits_exact ...              -- decoded operands on a grid are exact
```

`decode` returns `none` for NaN, infinities, subnormals, and biased exponents
below the bias (fractional values) — everything the development does not model.
Everything else comes back with the implicit leading significand bit restored
(`mant = 1024 + mantField`).

`fp16_bits_exact` takes the exponent bound *at the bit level*
(`e0 ≤ expField w - 15`) and uses `decode_some` to turn it into the `Fixed`
bound stage 38 needs, so the hypotheses are load-bearing rather than decorative.

`#eval decode 0x3C00` is `some { sign := false, mant := 1024, exp := 0 }` (1.0),
`#eval decode 0x7C00` is `none` (+inf). `#print axioms` on each reports only
`[propext, Quot.sound]`.

## Stage 44: a value domain with NaN and infinities

Stage 43 decoded the finite fragment and returned `none` for everything else.
`Intel/Fp16Value.lean` gives those classes values and proves how they behave.

```lean
inductive Fval                    -- nan | inf sign | fin v
def vstep ...                     -- NaN absorbs, infinities follow sign rules
def foldVal / foldFixed ...       -- value-depth and finite accumulation
theorem foldVal_fin ... :         -- all-finite operands give exactly foldFixed
    foldVal ... (.fin acc) n = .fin (foldFixed ... acc n)
theorem vstep_ne_fin_acc ...      -- non-finite accumulator stays non-finite
theorem foldVal_ne_fin ...        -- so does the whole fold
```

So the finite fragment is *closed*: finite operands produce exactly the
fixed-point result, and a non-finite accumulator never becomes finite again.

Not modeled: NaN payloads and subnormal values. Those are classes here, not
numbers, and the README says so.

`#print axioms` on each reports only `[propext]`.

## Stage 46: values for every finite fp16

Stage 43 returned `none` below the bias. `Intel/Fp16Scaled.lean` fixes a global
scale so *every* finite word has a concrete integer value, in units of `2 ^ -24`:

```lean
def scaled (w : Fp16) : Nat        -- 2 ^ 24 * value
theorem scaled_normal ...          -- (1024 + mantissa) * 2 ^ (exp - 1)
theorem scaled_subnormal ...       -- mantissa
```

Known vectors are checked with `decide`, which is what catches an off-by-one in
the bias or in the implicit leading bit:

| value | bits | `scaled` |
|---|---|---|
| 1.0 | `0x3C00` | `2 ^ 24` |
| 2.0 | `0x4000` | `2 ^ 25` |
| 0.5 | `0x3800` | `2 ^ 23` |
| 65504 (max) | `0x7BFF` | `65504 * 2 ^ 24` |
| `2 ^ -14` (min normal) | `0x0400` | `2 ^ 10` |
| `2 ^ -24` (min subnormal) | `0x0001` | `1` |

So subnormals and fractions are now numbers rather than classes.

The relation to the numeric layer's scale shows up as an executable fact in
stage 47: every normal decodes to a multiple of `2 ^ 14` in scaled units (the
`Fixed` grid), while the smallest subnormal has residue `1` — which is exactly
why a subnormal cannot be a `Fixed`. The general gluing lemma
`scaled = mag * 2 ^ 14` is still not proved; two attempts died on `whnf`
heartbeats while rewriting through `decode`, and the exactness results are
stated separately for `Fixed` and for bits, so nothing depends on it.

`#print axioms` on each theorem reports only `[propext, Quot.sound]`.

## Stage 47: executable checks for the fp16 path

`Intel/SmokeFp16.lean` runs the decoder and `scaled` on real bit patterns, all
with kernel `decide`:

- sign does not change the magnitude (`0xBC00` vs `0x3C00`);
- a depth-2 dot of A = [1.0, 2.0] and B = [2.0, 1.0] gives `2 ^ 49 + 2 ^ 49`;
- `1.0` plus the smallest subnormal is `2 ^ 24 + 1` in scaled units;
- `65504 * 1.0` is `65504 * 2 ^ 48`;
- **every normal is `0 mod 2 ^ 14`** in scaled units — the `Fixed` grid —
  while the smallest subnormal has residue `1`.

The last pair is the executable form of the scale gap: a subnormal genuinely
cannot be a `Fixed`.

## Stage 49: DPAS at instruction granularity

Assumption 5 said DPAS is one tile operation. `Intel/DpasAtom.lean` refines it:

```lean
theorem dpasSlab_split (dA rest) :
    dpasSlab (dA + rest) A B m n =
      dpasSlab dA A B m n +
        dpasSlab rest (A shifted by dA) (B shifted by dA) m n
theorem dpasSlab_two_atoms :
    -- the SYCL-TLA K tile: depth 32 is two atom instructions of depth 16
    dpasSlab 32 A B m n = dpasSlab 16 A B m n + dpasSlab 16 (shift 16) m n
```

The operand shift is the content: after an atom, the next instruction reads the
operands `dA` columns further along — the register rotation the kernel does.
So a tile DPAS is a chain of atom instructions, not a primitive.

`#print axioms` on each reports only `[propext, Quot.sound]`.

## Stage 50: interleaved copies

Stage 37's staging gives each lane a contiguous chunk. SYCL-TLA's copy atoms
interleave instead — lane `l` takes words `l, l + L, l + 2L, ...` — which needs
a copy whose *destination* is strided too:

```lean
def copyInterleaved (dstMem srcMem) (dst src stride) : Nat → Nat → Word
theorem copyInterleaved_value ...   -- every word comes from the matching offset
theorem copyInterleaved_frame ...   -- nothing else moves
```

Not done: composing the lanes into a workgroup copy and proving that the lanes
cover the slab. That needs the mod-`L` coverage argument, which is where the
earlier attempts stalled; this stage stops at the primitive rather than
overclaiming again.

`#print axioms` on each reports only `[propext, Quot.sound]`.

## Stage 51: residue classes for interleaved lanes

```lean
theorem lane_mod (L : Nat) :
    ∀ l l' t t', l < L → l' < L → l + t * L = l' + t' * L → l = l'
def lanesInterleaved ...        -- the workgroup copy, folded over lanes
```

Two lanes below `L` write different residue classes, so an interleaved copy can
never have two lanes collide: every earlier attempt to prove slab coverage died
on exactly this step.

Not proved: that the fold covers the slab. The residue argument is in place and
the fold induction that consumes it is not, so the ledger records assumption 8
as discharged up to the residue argument and no further.

`#print axioms lane_mod` reports only `[propext, Quot.sound]`.

## Stage 52: the audit covers every theorem

Stage 36 audited one headline theorem per stage. This stage audits all of them:

```
$ python3 Tools/check_axioms.py --all
KNOWN: IntelGpu.decode_gemmLoop also depends on Classical.choice (documented)
OK: all 200 theorems, 1 documented exception(s)
```

Discovery walks `Intel/**/*.lean` and runs `#print axioms` once per module, so a
dirty lemma anywhere — not just at a headline — fails the gate. The workflow now
runs `--all`.

Two things this caught in itself: the first sweep silently skipped
`Intel/Examples/` (so the one known exception vanished from the report), and the
helper had a 105-column line. Both fixed before the run that produced the result
above.

## Stage 53: known-answer tests for an fp16 dot

`Intel/SmokeFp16Dot.lean` checks whole dot products over bit patterns, the shape
a real kernel has — decode, scale, accumulate — against hand-computed values:

- A = [1.0, 0.5, 65504] with B = [1.0, 2.0, 1.0] gives `65506 * 2 ^ 48`;
- `1.0` times the smallest subnormal gives `2 ^ 24`;
- an empty dot is zero.

One test I wrote was **wrong** and `decide` refused it: I expected
`0xBC00 * 0x4000` to be negative, but `scaled` is a magnitude-only function —
the sign lives in `Fixed.sign`, not in `scaled`. The test now records the
actual behaviour and says why. That is exactly what these tests are for.

## Stage 54: the headline table regenerates itself

The README now carries a table of the audited headline theorems with their axiom
footprints, and `python3 Tools/check_axioms.py --md` regenerates it:

```
| # | Module | Headline theorem | Axioms |
|---|---|---|---|
| 1 | `Intel.AddOne` | `core_correct` | Quot.sound, propext |
...
| 4 | `Intel.Examples.GemmLoopDecoded` | `decode_gemmLoop` | Classical.choice |
```

Every row is `[propext]`, `[propext, Quot.sound]`, or the one documented
`Classical.choice` exception. The table is a curated subset — one headline per
layer — and says so; the numbers are table entries, not stage numbers, which the
caption also says because my first version labelled them "Stage" and would have
misled a reader.

## Stage 55: why the barrier is necessary

Stages 13-17 model SLM writes as visible at retire, which makes the barrier an
ordering annotation. `Intel/SlmLatency.lean` adds the minimal hazard — a write
lands in a pending buffer, reads see the committed copy, the barrier commits —
and proves the two facts that earn the barrier:

```lean
theorem stale_without_barrier :   -- no axioms: definitional
    stagedRead (stagedWrite s a v) a = s.committed a
theorem fresh_with_barrier :
    stagedRead (stagedBarrier (stagedWrite s a v)) a = v
theorem cross_lane_after_barrier :
    -- the barrier commits every pending write, not just this lane's
    stagedRead (stagedBarrier (stagedWrite s a v)) b = s.pending b
```

Skipping the barrier is a correctness bug, not a style choice.

I first wrote the cross-lane statement as `= s.committed b` and `simp` refused
it: the barrier exposes the whole pending buffer, so a *different* address reads
its pending value. The module records both the statement and the mistake.

## Stage 56: the two scales agree

Stage 46 fixes a scale of `2 ^ -24`; the numeric layer works in units of `2 ^ -10`
(normal) with `Fixed.mag`. `Intel/Fp16Gluing.lean` proves the relation:

```lean
theorem scaled_eq_mag (hne : expField w ≠ 0) (hge : 15 ≤ expField w) :
    scaled w = v.mant * 2 ^ v.exp * 2 ^ 14
theorem scaled_eq_mag' ... :
    scaled w = v.mag * 2 ^ 14
```

So a decoded word's scaled value is the `Fixed` magnitude times `2 ^ 14`, and the
grid results of stages 34 and 38 apply to decoded operands directly.

The field conditions are hypotheses. Deriving them from `decode w = some v`
needs the decoder's branch structure, and two earlier attempts died in
elaboration there; the conditions are exactly what `decode`'s branches
guarantee, and the module says so rather than pretending they are free.

`#print axioms` on each reports only `[propext, Quot.sound]`.

## Stage 57: interleaved staging, covered

The last blocked proof in the ledger. `Intel/InterleavedLanes.lean` now has:

```lean
theorem lanesInterleaved_frame ...   -- the fold leaves other words alone
theorem lanesInterleaved_value ...   -- lane l's word t comes from source t
theorem lanesInterleaved_covers ... :
    -- L lanes of n words at stride L fill [dst, dst + L * n)
    ∀ k < L * n, lanesInterleaved ... L (dst + k) = srcMem (src + k)
```

So assumption 8 is discharged in both shapes: contiguous chunks (stage 37) and
interleaved per-thread words (here), each with proven coverage.

It took six attempts. The fixes, in order of how much they mattered:

1. generalise the starting memory in the induction, as `laneBlockFold` needed;
2. apply the induction hypothesis with `exact ih …`, never `rw [ih …]`;
3. `simpa [Nat.add_assoc]` whenever the goal and lemma disagree on
   parenthesisation;
4. `Nat.div_lt_iff_lt_mul` wants `k < n * L`, not `L * n`;
5. `Nat.add_mul_mod_self_left` wants `l + L * t`, not `l + t * L` (stage 51).

Every failure was one of these five, and each cost an iteration because I fixed
it at the use site instead of understanding it first. `#eval` on the definition
(stage 55) ruled out the definition being wrong.

## Stage 58: what uniform control flow buys

Assumption 3 gives the workgroup one predicate, so lanes never diverge. This
stage states the hazard that rules out divergence:

```lean
def arrive (w : Parked) : Option Parked    -- retires only if all lanes parked
theorem barrier_needs_all_lanes :
    -- one lane missing ⇒ arrive w = none
theorem barrier_retires :
    -- every lane parked ⇒ the phase advances
```

A lane that took the other branch leaves the barrier stuck rather than letting
the workgroup proceed with a half-synchronised SLM. That is why the kernel's
control flow has to be uniform, and why stages 16/17 model it that way.

`#print axioms` on each reports only `[propext, Quot.sound]`.

## Stage 59: a SIMD lane dimension

Assumption 2 said there is one lane per step with no masks. `Intel/Simd.lean`
adds the lane dimension *on top of* the scalar core rather than rebuilding it:

```lean
structure Simd where            -- width, per-lane scalar states, mask
  width : Nat
  lanes : Nat → State
  mask : Nat → Bool
def simdRun ...                 -- active lanes run, masked lanes are untouched
theorem simdRun_active ...      -- an active lane is the scalar result
theorem simdRun_masked ...      -- a masked lane is unchanged
theorem add_one_simd ...        -- stage-1 correctness lifts to every active lane
```

Predication, not branching: `simdRun` runs the same instruction stream and
gates lanes by mask. So the scalar theorems apply per lane instead of being
re-derived — which is what the scalar model was for.

Still not modelled, and stated: GRF regions and sub-group packing.

`#print axioms`: the two `simdRun` lemmas use `[propext]`, `add_one_simd` uses
`[propext, Quot.sound]`.

## Stage 60: memory-model laws

Stage 1 defined `load32`/`store32` and proved only what `add_one` needed, so
every later frame argument re-derived the rest. `Intel/MemoryLaws.lean` collects
them once:

```lean
theorem store32_store32_same ...      -- last write wins at one address
theorem store32_store32_commute ...   -- stores at different words commute
theorem load32_store32_other ...      -- a load sees only its own address
theorem store32_eq_self ...           -- storing what is already there is a no-op
```

The abstraction stays what stage 1 said: one 32-bit word per aligned address,
word-addressed underneath. Alignment is an explicit precondition, not a silent
assumption.

`#print axioms`: `[propext]` or `[propext, Quot.sound]` throughout.

## Stage 61: NaN payloads

The last fully-open ledger item. `Fval.nan` now carries a payload, and the step
propagates it:

```lean
inductive Fval
  | nan (payload : Nat)
  | inf (neg : Bool)
  | fin (v : Fixed)
theorem vstep_nan_acc (pl) : vstep stepF (.nan pl) x y = .nan pl
theorem vstep_nan_left (pl) : (vstep stepF (.nan pl) x y).isNan = true
```

The rule is stated, not assumed: the accumulator's payload wins, then the first
operand's, then the second's. The isolation results of stage 44 are unchanged —
a non-finite accumulator still never becomes finite — so nothing downstream
moves.

`#print axioms` on each reports only `[propext]`.

## Not modeled yet

- IGC text parsing and register aliases (`r7:4`, `r12:2`).
- The compiler-generated prolog and global-id / address computation.
- SIMD masks, GRF regions, predicates, and scoreboards.
- SEND/EOT details beyond a halted flag.
- SLM bank layout and conflicts, sub-group masks, and barrier scheduling.
- Atomics and the launch ABI.
- IEEE-754 value semantics: stages 43-56 cover the bit layout, the value
  domain, values in units of `2 ^ -24` for normals, subnormals and fractions,
  and the glue between that scale and the numeric layer's. NaN *payloads*
  remain unmodeled.
- Instruction-level DPAS dispatch (the atom is modeled as a tile operation).
- Strided per-thread staging as SYCL-TLA's copy atoms use it: stage 37 models
  a block distribution (lane `l` owns a contiguous chunk), not the interleaved
  per-thread addressing.

## CI

`.github/workflows/build.yml` builds the `Intel` library and runs
`Tools/check_axioms.py` on every push and pull request. The audit is the gate:
a theorem that picks up an unexpected axiom fails the run, so the footprint
claims in this file cannot drift from the code.

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
19. Stage 19: the SYCL-TLA Xe GEMM instance.
20. Stage 20: partial K tail, so the instance holds for every K.
21. Stage 21: executed epilogue store and the end-to-end tile.
22. Stage 22: epilogue leading dimension.
23. Stage 23: assembling executed tiles into `GemmSpecW`.
24. Stage 24: operand staging from global memory into SLM.
25. Stage 25: the composed mainloop (stage, sync, DPAS).
26. Stage 26: the full tile pipeline (mainloop + epilogue).
27. Stage 27: rounding contract and accumulation error bound.
28. Stage 28: executed tail slab, so the pipeline covers every K.
29. Stage 29: concrete truncating rounding, deriving the contract.
30. Stage 30: round-to-nearest, halving the accumulation bound.
31. Stage 31: ties-to-even, the hardware tie rule.
32. Stage 32: bridging word arithmetic to the numeric bound.
33. Stage 33: executable smoke tests.
34. Stage 34: exactness on a shared quantization grid.
35. Stage 35: executable checks for the workgroup stages.
36. Stage 36: axiom audit over the whole stack.
37. Stage 37: distributed staging across lanes.
38. Stage 38: fp16-shaped values on a shared grid.
39. Stage 39: the epilogue is a frame-preserving write.
40. Stage 40: one output buffer for all tiles (frame law).
41. Stage 41: blocks are separated.
42. Stage 42: the shared buffer is complete.
43. Stage 43: a bit-level fp16 encoding.
44. Stage 44: a value domain with NaN and infinities.
45. Stage 45: CI builds the library and runs the axiom audit.
46. Stage 46: values for every finite fp16.
47. Stage 47: executable checks for the fp16 path.
48. Stage 48: consolidate the assumption ledger.
49. Stage 49: DPAS at instruction granularity.
50. Stage 50: interleaved copies.
51. Stage 51: residue classes for interleaved lanes.
52. Stage 52: the audit covers every theorem.
53. Stage 53: known-answer tests for an fp16 dot.
54. Stage 54: the headline table regenerates itself.
55. Stage 55: why the barrier is necessary.
56. Stage 56: the two scales agree.
57. Stage 57: interleaved staging, covered.
58. Stage 58: what uniform control flow buys.
59. Stage 59: a SIMD lane dimension.
60. Stage 60: memory-model laws.
61. Stage 61 (this PR): NaN payloads.
