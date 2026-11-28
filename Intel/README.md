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

10. **Transcription fidelity** — `Intel/Examples/RealAddOne.lean` is a hand
    transcription of a real IGC dump (sha256 `1a4889be…`), not a parsed one.
    The correspondence is checked by comparing the module against the quoted
    dump; a parser is what stage 63 starts to build. The dump's platform line
    and build-option string name a product and are redacted.

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

## Stage 62: a real IGC kernel, imported

Issue #63's first P0 item: import unmodified compiler output and record its
provenance. `Intel/Examples/RealAddOne.lean` is the `_main_0` function IGC
emitted for a five-line SYCL `parallel_for` add-one, transcribed verbatim with
execution sizes intact:

```
mul  (M1_NM, 1) V0044 V0038 V0036     shl (M1, 32) V0051 V0048 0x2:q
mov  (M1, 32)   V0045 V0046           add (M1, 32) V0052 V0051 V0050
add3 (M1, 32)   V0047 V0044 V0045 V0037
lsc_load.ugm (M1, 32) V0054:d32 flat[V0053]:a64
add  (M1, 32)   V0055 V0054 0x1:w
lsc_store.ugm (M1, 32) flat[V0053]:a64 V0055:d32
```

Provenance (compiler version, `zeinfo` format, kernel attributes, dump hash) is
in the module. The dump's platform line and build-option string name a product
and are redacted, as the project's own rule requires.

## Stage 62b: the decoder's coverage, as a theorem

`Intel/RealCoverage.lean` answers the review's "reject unsupported instructions
explicitly" with proofs, not impressions:

```lean
theorem realAddOne_rejected :
    rejected realAddOne = ["or", "mul", "mov", "add3", "mov", "shl", "add",
                           "lsc_load.ugm", "add", "lsc_store.ugm", "ret"]
theorem realAddOne_unsupported : decodeProgram realAddOne = none
```

The stage-5 decoder reads **none** of the real kernel: region syntax, arity and
unknown opcodes all fail closed. That is the gap stages 63+ exist to close, and
it is now measured.

## Stage 63: decoding the real kernel, failing closed

`Intel/RealDecode.lean` decodes exactly the instruction forms the real add-one
kernel uses, and refuses everything else:

- `Grf` keeps the full region: register number, row and column offsets,
  vertical stride, region width and horizontal stride. IGC's `<v>` shorthand is
  normalised to `<v;1,0>`; any other spelling is refused.
- `parseExec` reads the execution size from after the comma, so `(M1, 32)` and
  `(M1_NM, 1)` both parse while `(M1, 32, 7)` does not.
- Typed suffixes are read literally after the colon (`d32`, `a64`, `q`, `w`,
  `ud`); immediates are parsed as hex or decimal (`0x2:q`, `0x1:w`).
- `lsc_load.ugm` and `lsc_store.ugm` name their payload as a bare register in
  IGC's output, so those operands are register numbers, not regions.

The correspondence is a set of kernel-checked theorems:

```lean
theorem realAddOne_decodes : (decodeRealProgram realAddOne).isSome = true
theorem realAddOne_decoded_length : ... = some 11
theorem realAddOne_load  : ... is[7]? = some (.load 32 54 .d32 53)
theorem realAddOne_addImm: ... is[8]? = some (.addImm 32 V55 V54 1 .w16)
theorem realAddOne_store : ... is[9]? = some (.store 32 53 .d32 55)
```

Negative tests pin the fail-closed behaviour: a malformed execution size, a
truncated instruction and a load payload written as a region all return `none`.

Parsing is structural on `List Char` (no `String.splitOn`), so the proofs
reduce in the kernel. The program-level proofs `unfold` the two decoder
definitions and then `decide`; the audit records the `Classical.choice`
dependency inherited from `String.toList`, as for the stage-5 decoder.

## Stage 64: executing the real kernel

`Intel/RealSemantics.lean` runs the decoded program. The dump's `.decl` table
answered the one question the listing left open: `V0053` is not an independent
register, it is `alias=<V0052, 0>`, the unsigned 64-bit view of the computed
address. The model therefore carries the dump's numeric aliases:

```
V0046 -> V0039     V0049 -> V0047     V0050 -> V0034     V0053 -> V0052
```

(`V0033` and `V0036` alias `%r0`; the kernel only reads them, so they are
independent inputs here.)

Registers are 64-bit element slots. The destination's declared type chooses a
32-bit operation with zero-extension (`d32`) or a full 64-bit operation (`q64`);
the types and element counts come from the dump's `.decl` lines. Source regions
are interpreted exactly as far as this kernel needs: `(0,0)<0;1,0>` broadcasts
element 0 and `(0,0)<1>`/`(0,0)<1;1,0>` is dense, lane `l` reading element `l`.
Two `decide` theorems pin the assumptions: every destination is `(0,0)`, width
1, horizontal stride 0 (`realAddOne_regions_simple`), and every destination
register's element count equals the execution size (`realAddOne_dst_counts`).

The `or` prologue writes `%cr0`, which no later instruction reads, and is a
no-op in the model. The address chain is proved end to end (the model is total,
so the identity is stated for every lane index; the effect theorem restricts to
the 32-lane launch):

```lean
theorem realAddOne_address_preamble :
    readSrc (runReal s realAddOnePreamble) ⟨53,0,0,1,1,0⟩ l =
      realAddress base (threadId localSize r0 localId globalOffset l)

realAddress base id = (zeroExtend id) <<< 2 + base
threadId ... l    = localSize * r0 + localId l + globalOffset
```

This is `%12 = (%9 << 2) + %10` from the dump's source IR, with `%8` computed in
32-bit arithmetic as the IGC `d32` sequence does. The memory half is
`realAddOne_effect`: the kernel halts, each of the 32 lanes gets an aligned
address, the word originally at each lane's address is incremented, and every
other word is unchanged. Distinct word addresses are the race-freedom
hypothesis. When addresses alias, `storeVec` uses `Classical.choose` to pick a
lane; that is why the stage-64 theorems carry the documented
`Classical.choice` exception.

Still trusted: that the hardware implements these instructions as modelled.
The alias table, types and element counts are transcribed from the dump, and
the assembly-to-program correspondence is `realAddOne_decoded_eq`.

## Stage 65: a real GEMM, imported

`Intel/Examples/RealGemm.lean` is the `_main_0` body IGC emitted for a
64x64x64 `int` GEMM, one work-item per output, generated directly from the
dump by `Tools/parse_igc.py`. Provenance is in the module: oneAPI 2026.1 IGC,
`zeinfo` 1.71, `SimdSize=32`, `PerThreadInputSize=128`, and the sha256 of the
unredacted dump `70d71a09…5368`; the platform line and build-option string are
redacted. The parser now keeps an execution size such as `(M1_NM, 1)` as one
operand, keeps a predicated `(!P1) goto` as one opcode, and skips directives and
`FILE`/`LOC` markers, so the statement list is machine-generated rather than
hand-transcribed.

`Intel/RealGemmCoverage.lean` measures the decoder against it:

```lean
theorem realGemm_accepted : acceptedReal realGemm = [27 opcodes]
theorem realGemm_rejectedOps :
    rejectedOps realGemm = ["mov", "mov", "or", "cmp.lt", "(!P1) goto", "goto"]
theorem realGemm_rejectedLabels :
    rejectedLabels realGemm = ["_main_0", "_0_004", "_0_006", "_0_005"]
theorem realGemm_not_decoded : decodeRealProgram realGemm = none
```

So the stage-63 decoder already reads 27 of the 33 instructions: the index
arithmetic, both `lsc_load.ugm`, the multiply-add, the store and `ret`. What it
refuses is exactly the control-flow shell: the two `mov 0x0:d` initialisers,
the loop `or`, `cmp.lt`, `goto`, the predicated exit, and labels. Those are the
next stage, not a surprise.

## Stage 66: the GEMM's control-flow shell

Stage 65 left six instructions and every label undecoded. This stage closes
that list:

- `RInstr` gains `label`, `movImm`, `or`, `cmpLt`, `goto` and `gotoIf`.
- `parseWidth` accepts IGC's `:d` dword suffix, which the two `mov 0x0:d`
  zero-initialisers use.
- `RealState` gains a uniform predicate file; `cmp.lt` writes lane 0's
  comparison. `runRealCF` is a fuel-based interpreter for labels, `goto` and
  the predicated `(!P1) goto`, so branch targets are resolved rather than
  dropped. The add-one proofs still use the straight-line `runReal`.

The coverage module now proves closure:

```lean
theorem realGemm_accepted : acceptedReal realGemm = [33 opcodes]
theorem realGemm_rejectedOps : rejectedOps realGemm = []
theorem realGemm_rejectedLabels : rejectedLabels realGemm = []
theorem realGemm_decodes : (decodeRealProgram realGemm).isSome = true
theorem realGemm_decoded_length : ... = some 37
```

The four branch targets also resolve in the decoded list:
`_main_0` at 0, `_0_004` at 11, `_0_006` at 27 and `_0_005` at 30. What remains
is the functional loop proof: the next GEMM stage connects this decoded loop
to the existing `sum += A[i*K+k] * B[k*N+j]` memory-loop invariant.

## Stage 67: byte-addressed memory

The word-addressed model is refined to bytes:

- `load32LE` / `store32LE` over `Nat → BitVec 8`, little-endian.
- `load32LE_store32LE_same`, `store32LE_frame`, and
  `load32LE_store32LE_other` for a disjoint four-byte range.
- `wordView_store32LE`: an aligned byte store is exactly a word store in the
  stage-1 view. `wordView` is the bridge between the two layers.
- `byteDisjoint` and `wordDisjoint_byteDisjoint`: distinct aligned word indices
  give disjoint byte ranges.
- `realAddOne_byteRangesDisjoint`: the real add-one kernel's 32 lane writes are
  pairwise byte-disjoint under the stage-64 distinctness hypothesis.
- `realAddOne_byte_word_increment`: the final word at each lane, read through
  the byte view, is the original little-endian word plus one.

Visibility, synchronization and a full hardware memory model remain open; this
stage covers byte-level accesses, alignment, aliasing and race freedom at byte
granularity.

## Stage 68: the GEMM's own tables and loop entry

The semantics is now parameterised rather than add-one-specific:
`stepWith alias typeOf` takes the register-alias and declared-type tables, and
`runRealWith` is the generic straight-line fold. `stepReal`/`runReal` are the
add-one instances, so all earlier proofs are unchanged.

`Intel/GemmReal.lean` instantiates both tables from the real GEMM dump:

```
gemmAlias    V0052 -> V0042   V0056 -> V0041   V0059 -> V0034   V0060 -> V0035
             V0065 -> V0063   V0068 -> V0067   V0073 -> V0071   V0076 -> V0075
             V0079 -> V0061   V0081 -> V0036   V0083 -> V0080   V0086 -> V0085
gemmRegType / gemmRegElems   the dump's `.decl` types and element counts
```

The first 11 statements are proved to be a prefix of the decoded program
(`realGemm_preamble_prefix`), and the preamble's executions are proved:

```lean
gemmI  = localSizeY * r0[6] + zeroExtend(localIdY) + globalOffset[1]
gemmJ0 = localSizeX * r0[1] + zeroExtend(localIdX)

theorem gemmPreamble_entry :
    V0058 = zeroExtend (gemmI <<< 6) ∧
    V0057 = zeroExtend gemmJ0 ∧
    V0061 = 0 ∧ V0062 = 0
```

`gemmPreamble_dst_counts` checks every preamble destination against its
declared type and element count, so whole-register writes stay exact. The next
GEMM stage is the loop body: the two address chains, the load/multiply/add and
the counter/branch, followed by the K-induction and the final store.

## Stage 69: GEMM loop-body indices

`GemmLoopInv` records the loop-head values: `V0058 = i << 6`, `V0057 = j0`,
`V0061 = k`, `V0062 = sum`, the three pointers, and `globalOffset[0]`.
`gemmIndexBlock` is the first half of the loop body: the `or`/moves/shifts for
the A address and the `shl`/`add3` for the B index.

The address step is a bitwise `or` used as an add: `V0063 = V0058 | V0061`.
`or_shift_six` proves `(i << 6) ||| k = i * 64 + k` for `i, k < 64`, checked
over `Fin 64` by kernel `decide`; `shl_six` records `k << 6 = k * 64`.

```lean
theorem gemmIndexA : V0063 = zeroExtend (i * 64 + k)
theorem gemmIndexB : V0071 = zeroExtend (k * 64 + j0 + globalOffset[0])
```

Next is the byte-address half: converting `A + 4 * index` to a word index,
the two loads, and the multiply-add.

## Stage 70: GEMM loop-body loads and accumulation

`gemmAddressBlock` extends the index block with the B move/shift/add, and the
byte addresses are proved:

```lean
theorem gemmAddressA : V0067 = (zeroExtend (i * 64 + k)) <<< 2 + aPtr
theorem gemmAddressB : V0075 = (zeroExtend (k * 64 + j0 + goX)) <<< 2 + bPtr
```

`wordOf_ptr_add_shift` (and its `Nat` form) converts an aligned pointer plus a
four-byte index to a word index. `gemmBodyBlock` is the complete memory half:
both address chains, `lsc_load` for A and B, the multiply and the accumulate.
`gemmBody` states all four results:

```lean
loadA   = mem (aPtr / 4 + i*64 + k)
loadB   = mem (bPtr / 4 + k*64 + j0 + goX)
product = loadA * loadB
sum'    = sum + loadA * loadB
```

The remaining loop proof is the `cmp.lt`/`goto` control flow, the counter
increment, the K-induction and the epilogue store.

## Stage 71: one real loop iteration

`gemmBodyStep` is the complete executed iteration: the body block, `cmp.lt`
against 63, and the counter increment. `gemmBodyStep_inv` is the inductive
step:

```lean
theorem gemmBodyStep_inv :
    GemmLoopInv (runGemm s gemmBodyStep) ... (k + 1)
      (sum + memA * memB) ∧
    (runGemm s gemmBodyStep).preds 1 = true ∧
    (runGemm s gemmBodyStep).mem = s.mem
```

The supporting lemmas isolate the tail: `gemmBodyStep_counter` gives
`V0061 = k + 1`, `gemmBodyStep_pred` gives `P1 = (k < 63)`, `gemmBodyStep_sum`
gives the new `V0062`, and `gemmBodyStep_frame` shows the row shift, column
base, pointers and memory are untouched.

What remains is the K-induction over repeated steps, the final body at
`k = 63` (where the predicate is false and the counter is not incremented),
and the epilogue store to `C`.

## Stage 72: the GEMM invariant is per-lane

`GemmLoopInv` now takes the lane:

```lean
structure GemmLoopInv (s : RealState) (aPtr bPtr cPtr : Addr) (l : Nat)
    (i j0 k sum goX : Word) : Prop where
  v58 : s.regs 58 l = zext (i <<< 6)
  v57 : s.regs 57 l = zext j0
  v61 : s.regs 61 0 = zext k
  v62 : s.regs 62 l = zext sum
  ...
```

This is what the launch supplies: each lane has its own row `i`, column base
`j0` and accumulator `sum`, while the K counter `V0061` is uniform. The earlier
`∀ l` fields forced one `i/j0/sum` across the whole warp, which no real launch
satisfies; this stage corrects that.

All stage 68-71 proofs were updated, and `gemmBodyStep_inv` is now a genuinely
per-lane inductive step. The distributed `setWidth` forms of the OR and address
expressions needed the 64-bit and `Nat` variants `or_shift_six_64`,
`nat_wordA`/`nat_wordB`/`nat_wordB_mod`.

Next is the K-induction over repeated per-lane steps and the epilogue store.

## Stage 73: the GEMM epilogue address

`gemmEpilogue` is the exit path: `add3` computes the C index `i*64 + j0 +
globalOffset[0]` in `V0080`, `mov`/`shl`/`add` turn it into the C byte address
`V0085`, then `lsc_store` writes `V0062` and the kernel returns.

```lean
theorem gemmEpilogue_address :
    (runGemm s gemmEpilogue).regs 85 l =
      (zext (i * 64 + j0 + goX)) <<< 2 + cPtr
```

The store itself writes the per-lane sum `V0062` at that address; its
word-level correctness needs the per-lane distinctness hypothesis and is the
next step, together with the K-induction over repeated loop steps.

## Stage 74: the GEMM K-induction

`Intel/GemmRealLoop.lean` iterates the one-step invariant without unfolding a
whole program. `gemmStepIter n s` applies `runGemm s gemmBodyStep` exactly `n`
times, and `gemmDot` accumulates one term per step:

```
gemmDot k 0       = 0
gemmDot k (n + 1) = gemmTerm k + gemmDot (k + 1) n
```

```lean
theorem gemmStepIter_inv :
    GemmLoopInv (gemmStepIter n s) ... l i j0 (k + n)
      (sum + gemmDot s.mem ... k n) goX ∧
    (gemmStepIter n s).mem = s.mem
```

This is the K-induction. Stating it as a recursion on states rather than a
list-append fold keeps the kernel obligations small; the earlier list-based
attempt timed out on whole-state unfolding.

The remaining GEMM pieces are the final body at `k = 63` (where `cmp.lt` is
false and the counter is not incremented), the sum `gemmDot 0 64`, and the
epilogue store at `C`.

## Stage 75: the final iteration and the total sum

`gemmFinalStep` is the `k = 63` iteration: the body plus `cmp.lt`, without the
counter increment. `gemmFinalStep_inv` proves the invariant at the same `k`
with `sum + gemmTerm k`, the exit predicate `P1 = (k < 63)`, and unchanged
memory.

`gemmDot_append` shows that the last term is appended at counter `k + n`, and
`gemmLoop_final` composes the whole loop:

```lean
theorem gemmLoop_final :
    GemmLoopInv (runGemm (gemmStepIter 63 s) gemmFinalStep) ... 63
      (gemmDot s.mem (aPtr/4) (bPtr/4) i j0 goX 0 64) goX ∧
    (runGemm (gemmStepIter 63 s) gemmFinalStep).preds 1 = false ∧
    (runGemm (gemmStepIter 63 s) gemmFinalStep).mem = s.mem
```

So 63 loop steps plus the final body accumulate all 64 terms and leave the
exit predicate false. The remaining piece is the epilogue store at `C` and the
final output statement.

## Stage 76: the epilogue store at C

`gemmEpilogue_mem` exposes the exact store vector of the epilogue:

```lean
theorem gemmEpilogue_mem :
    (runGemm s gemmEpilogue).mem =
      storeVec s.mem 32 ((runGemm s gemmEpilogue).regs 85)
        (fun l => low32 (s.regs 62 l))
```

At lane `l`, with a word index `w` equal to the C address divided by four and
the per-lane distinctness hypothesis, `gemmEpilogue_store_at` gives
`storeVec ... w = sum`, and `gemmEpilogue_store_mem` gives the final memory:

```lean
theorem gemmEpilogue_store_mem :
    (runGemm s gemmEpilogue).mem w = sum
```

The explicit `w` keeps the dependent index out of the statement; the final
output theorem will instantiate `w = cPtr/4 + (i*64+j0+goX).toNat`.

## Stage 77: the real GEMM's end-to-end output

`realGemm_output` composes the loop, the final body and the epilogue:

```lean
theorem realGemm_output :
    (runGemm (runGemm (gemmStepIter 63 s) gemmFinalStep) gemmEpilogue).mem w =
      gemmDot s.mem (aPtr/4) (bPtr/4) i j0 goX 0 64 ∧
    (runGemm (runGemm (gemmStepIter 63 s) gemmFinalStep) gemmEpilogue).halted = true
```

for a lane `l < 32`, an admitted launch (`GemmLoopInv` at `k = 0`, `sum = 0`,
plus the pointer/index bounds), aligned A/B/C pointers, and
`w = cPtr/4 + (i*64+j0+goX).toNat`.
`nat_wordC` turns the C byte address into that word index, and
`gemmEpilogue_halted` covers the return.

So one real, unmodified IGC `_main_0` integer GEMM is now decoded, executed,
and proved to write `C[i*64+j] = sum_k A[i*64+k] * B[k*64+j]`, under the
stated alignment, bounds and per-lane (race-freedom) hypotheses.

## Stage 78: SEND, SBID and the register scoreboard

`Intel/SendSbid.lean` models the SEND mechanism behind `lsc_load.ugm` and
`lsc_store.ugm`:

- `issueLoad` / `issueStore` assign a fresh token (an SBID), mark it pending,
  and capture the load's memory value or the store's value.
- `complete` marks a token done; `wait` succeeds only on a done token.
- `commitLoad` writes a completed load's captured value to its destination
  register; `commitStore` writes a completed store's value to memory.
- `loadPipeline`, `storePipeline` and `addOnePipeline` are the load-add-store
  shape of the real add-one kernel.

The proved part of the contract:

```lean
theorem wait_pending : ... -> wait s t = none
theorem wait_done    : ... -> wait s t = some s
theorem loadPipeline_value  : (loadPipeline s reg addr).regs reg = s.mem addr
theorem storePipeline_value : (storePipeline s addr val).mem addr = val
theorem addOnePipeline_value : (addOnePipeline s addr reg tmp).mem addr = s.mem addr + 1
```

`SendAssumptions` and the module header name the modelled-but-not-printed part:
fair completion, sample-at-issue memory, the register scoreboard as the wait,
and no token reuse while pending. The assembly text does not print SBIDs, so
those are assumptions, not facts read from the dump.

## Stage 79: a real DPAS instruction, decoded

The DPAS model's two-atom split (`dpasSlab_two_atoms`) is the 8x16x16
SYCL-TLA atom. A real compiled FMHA fp8 kernel uses a different shape:

```
dpas.8x8 (16|M0) r383:f null:f r39:hf8 r335.0:hf8 {Atomic,Fwd,$6.dst}
```

`Intel/RealDpas.lean` records the instruction with provenance (sha256
`b0449b8c…85a3`, platform/options redacted) and decodes it:

```lean
theorem realFmhaDpas_form :
    parseDpas "dpas.8x8" "(16|M0)" "r383:f" "r39:hf8" "r335.0:hf8" =
      some ⟨.m8n8, 16, .hf8, .f32⟩
theorem fmhaDpas_not_tlaAtom : DpasShape.m8n8 ≠ DpasShape.m8n16
theorem fmhaDpas_depth : DpasType.hf8.k = 32
```

So the compiled FMHA atom is 8x8x32 with an `f32` accumulator, not the
model's 8x16x16. The existing `dpasSlab_two_atoms` theorem stays scoped to the
SYCL-TLA fp16/fp32 configuration; the fp8 FMHA path needs its own 8x8x32 atom.
That is a mapping result the review asked for, and it is a negative one.

## Stage 80: zero times infinity is invalid

`Fp16Value.vstep` treats every finite operand times an infinity as an
infinity. IEEE-754 makes `0 * inf` an invalid operation. `Intel/Fp16Ieee.lean`
adds the refined step:

- `vstepIEEE`: NaN absorbs; `inf * inf` keeps the same sign and is NaN for
  opposite signs; zero times an infinity is NaN; a non-zero finite operand
  times an infinity is an infinity.
- `vstepIEEE_zero_left` / `vstepIEEE_zero_right`: the invalid cases, with
  payload `0`.
- `foldValIEEE_fin`: all-finite operands still compute exactly the machine
  accumulation.
- `foldValIEEE_ne_fin`: a non-finite accumulator never becomes finite.
- `vstep_zero_inf_old`: the old step returns an infinity there, so the
  refinement changes exactly the invalid operation.

The payload policy is explicit: an invalid operation produces `NaN` with
payload `0`; the stage-61 NaN-payload propagation rules are unchanged. This is
not yet a full IEEE FMA: subnormals, exponent overflow/underflow, signed zero
and rounding are still outside the class model.

## Stage 81: hardware conformance for the real GEMM

Issue #63's P1 conformance item: a differential test between actual Intel GPU
execution and the formal model.

- `Tools/conformance/gemm_conformance.cpp` runs the 64x64x64 integer GEMM with
  the dump's source shape and deterministic inputs, checks every output against
  a CPU reference, and prints a 32-bit checksum.
- `Tools/conformance/gemm_eval.lean` evaluates the Lean `gemmDot` on the same
  inputs.
- Recorded run: compiler oneAPI 2026.2.0, Level-Zero runtime 1.18.40867; the
  device is an Intel discrete GPU with product/PCI details withheld per policy.

Result: the GPU prints `C00=-2 C11=-5 C6363=4 checksum=4294967290 bad=0`; the
Lean model's unsigned forms are `4294967294 4294967291 4` and its full
4096-output checksum is `4294967290`. Both sides agree bit-for-bit.

This is a conformance test, not a proof; the end-to-end theorem remains
`realGemm_output`. The dump was compiled with oneAPI 2026.1 and this run with
2026.2, so it tests the source-level kernel semantics on the same GPU family,
not the exact binary.

## Stage 82: a real SIMD vector add, imported

A second real kernel, generated on the Intel GPU with IGC dumps:
`c[i] = a[i] + b[i]` over 1024 `int`s, oneAPI DPC++ 2026.2.0, `zeinfo` 1.74,
`SimdSize=32`, `PerThreadInputSize=64`, sha256 `9efa09a6…b928`; platform and
options redacted. `Intel/Examples/RealVectorAdd.lean` is generated by
`Tools/parse_igc.py`; predicated mnemonics such as `(!P3) goto` and `(P6) sel`
are kept as one opcode.

This dump introduces the SIMD forms the add-one/GEMM dumps did not use:

- masked `(M5, 16)` moves,
- `cmp` against a register, predicate `and`/`or`,
- `sel` under a predicate,
- scaled `flat(base)[0x4*index]` loads and stores.

The coverage module measures the gap: the decoder reads 18 of 41 instructions
and refuses 23 (`realVectorAdd_rejectedOps`). Labels decode.

It also exposed a fail-closed hole: `parseExec` used to ignore the mask, so
`(M5, 16)` would have been read as `(M1, 16)`. It now accepts only M1/M1_NM;
`masked_mov_rejected` proves the M5 form is refused. The hardware run of this
kernel printed `bad=0 sum=4294967289`.

Next: predicate/mask/`sel` semantics and scaled memory operands, then the
vector-add effect theorem.

## Stage 83: scaled memory and a straight-line vector add

The straight-line `nd_range` vector add introduces a scaled global operand:

```
lsc_load.ugm  V0057:d32  flat(V0056)[0x4*V0055]:a32u
lsc_store.ugm flat(V0061)[0x4*V0055]:a32u  V0060:d32
```

`loadScaled` / `storeScaled` now decode this form: a scalar base register plus
a per-lane 32-bit index at byte scale four. The semantics computes
`base + (index <<< 2)` and reads the base at element zero (`readScalarWith`).

`Intel/Examples/RealVectorAddFlat.lean` is generated from the real dump
(oneAPI DPC++ 2026.2.0, `zeinfo` 1.74, `SimdSize=32`,
`PerThreadInputSize=64`, sha256 `d05c6952…30d4`, platform/options redacted).
`Intel/VectorAdd.lean` adds the `.decl` tables and proves the index:

```lean
vaId = localSize * r0 + zeroExtend(localId) + globalOffset
theorem vaPreamble_id : V0055 = zeroExtend (vaId ...)
theorem realVectorAddFlat_decoded_length : ... = some 10
```

The whole straight-line kernel decodes, including the scaled loads and store.
The loop vector-add's coverage moves from 18/41 to 21/41; the remaining 20
refusals are the masked moves, predicate `cmp`/`and`/`or`, `sel` and the
predicated `goto`s. The hardware run of the `nd_range` source is `bad=0`.

Next: the load/add/store effect for this kernel, giving
`c[id] = a[id] + b[id]` per lane.

## Stage 84: the vector add's loads and sum

With the scaled address decoded, the straight-line vector add's data path is
proved:

```lean
theorem vaLoadA : V0057 = zeroExtend (mem (aWord + id))
theorem vaLoadB : V0059 = zeroExtend (mem (bWord + id))
theorem vaAdd   : V0060 = zeroExtend (mem (aWord + id) + mem (bWord + id))
theorem vaTail_halted : (runVA s (vaPreamble ++ vaTail)).halted = true
```

`vaWordNat` turns the scaled address `base + 4*index` into the word index
`base/4 + index`; `vaPreamble_pointers` and `vaPreamble_mem` carry the pointer
and memory frame through the preamble.

The remaining piece is the scaled store and its frame: `c[id] = a[id] + b[id]`
at each lane, with unrelated words unchanged.

## Stage 85: the real vector add, end to end

`vaMem` exposes the final memory as a store vector over the C addresses; then
`vaStore` and `vaFrame` give the effect:

```lean
theorem realVectorAdd_effect :
    (runVA s (vaPreamble ++ vaTail)).halted = true ∧
    (runVA ...).mem (cPtr/4 + id l) =
      s.mem (aPtr/4 + id l) + s.mem (bPtr/4 + id l) ∧
    (∀ w, (∀ l', l' < 32 -> w ≠ cPtr/4 + id l') ->
      (runVA ...).mem w = s.mem w)
```

So the real, straight-line `nd_range` SIMD vector add writes
`c[i] = a[i] + b[i]` at each lane, preserves every unrelated word, and halts,
under aligned A/B/C pointers, the index bounds and per-lane distinctness. The
hardware run of the same source is `bad=0`.

## Stage 86: DPAS atom shapes, quantified

The real FMHA form and the SYCL-TLA atom are now both recorded as data:

```lean
def tlaXeF16Atom : DpasAtomShape := ⟨8, 16, 16, .f16, .f32⟩
def fmhaFp8Atom  : DpasAtomShape := ⟨8, 8, 32, .hf8, .f32⟩
```

`realFmhaDpas_atom` ties the decoded `dpas.8x8` instruction to the FMHA atom;
`fmha_atom_not_tla` records the N difference. `atomsPerTile` quantifies the
consequence for a K=32 tile:

```lean
theorem fmha_fp8_k32_atoms : atomsPerTile fmhaFp8Atom.k 32 = 1
theorem tla_f16_k32_atoms  : atomsPerTile tlaXeF16Atom.k 32 = 2
```

So the compiled FMHA fp8 mainloop issues one 8x8x32 DPAS per K=32, while the
SYCL-TLA fp16 path issues two 8x16x16 DPAS instructions — the existing
`dpasSlab_two_atoms` split. The atom mapping is now explicit in both directions.

## Review #63 response

`Intel/REVIEW_63.md` maps every priority in the review to the stages and
artifacts that address it, lists the acceptance criteria, and separates the
trusted base from the remaining open work.

## Stage 88: the 8x8x32 atom's dataflow

`fmhaAtom` gives the decoded FMHA fp8 atom a mathematical operation: accumulate
a depth-32 dot into an 8x8 C tile at `(i, j)`.

```lean
theorem fmhaAtom_correct :
    fmhaAtom A B C i j m n =
      C (i + m) (j + n) + dotMatFrom A B (i + m) (j + n) 0 32
theorem fmhaAtom_shape : fmhaFp8Atom.m = 8 ∧ ... .n = 8 ∧ ... .k = 32
```

So the decoded 8x8x32 form is tied both to its operand types (stage 79/86)
and to the depth-32 matrix dot (via `dpasSlab_eq_dotMatFrom`). Register packing
and the operand layout of the real `r39:hf8`/`r335.0:hf8` pair, and the FMHA
kernel execution, remain open.

## Stage 89: negative tests for scale and wait

Two load-bearing negative results, complementing the decoder rejections:

```lean
theorem va_scale_load_bearing :
    ((0 + (zext 1 : Addr)) <<< 2).toNat / 4 = 1 ∧
    (0 + zext 1 : Addr).toNat / 4 = 0
theorem wait_issueLoad_stalls  : wait (issueLoad s reg addr) s.next = none
theorem wait_issueStore_stalls : wait (issueStore s addr val) s.next = none
theorem commitLoad_pending  : commitLoad s t reg = s   -- when t is pending
theorem commitStore_pending : commitStore s t addr = s -- when t is pending
```

The first shows a wrong address calculation (dropping the four-byte scale)
hits a different word. The SEND lemmas show that waiting or committing before
completion stalls or writes nothing, so the model cannot silently observe an
in-flight value.

## Stage 90: per-lane predicates

`RealState.preds` is now indexed by predicate and lane. `cmp.lt` writes the
comparison on every active lane; a different predicate or an inactive lane is
untouched:

```lean
theorem cmpLt_lane     : (cmpLt n p src imm w).preds p l = decide (low32 (src l) < imm)
theorem cmpLt_other    : p' ≠ p -> (cmpLt ...).preds p' l = s.preds p' l
theorem cmpLt_inactive : ¬ l < n -> (cmpLt ...).preds p l = s.preds p l
```

The GEMM's uniform branch reads lane 0 (`runRealCF`), so all its control-flow
proofs are unchanged; the vector-add loop's per-lane predicate logic now has a
model to build on. Execution masks `(M1, …, M5, …)`, `sel`, predicated `goto`
and the grid-stride loop remain.

## Stage 91: predicated select

The decoder now accepts the vector-add dump's `(P6) sel` form, and `stepWith`
selects each lane independently:

```lean
theorem sel_lane : (stepWith alias typeOf s (.sel n p dst a b)).regs (alias dst.num) l
  = if s.preds p l then readSrcWith alias s a l else readSrcWith alias s b l
```

Both the destination region check and the GEMM destination-count invariant cover
the new instruction. The vector-add decoder's accepted list therefore includes
the two selects; only the M5 masks, predicate `and`/`or` and predicated `goto`s
remain rejected in that dump.

## Stage 92: execution masks decoded

`parseExec` now returns an `Exec` record rather than a bare size:

```lean
structure Exec where
  size   : Nat
  offset : Nat
  noMask : Bool
```

The offset follows the vISA M1-M8 table (M1 = 0, M2 = 4, …, M5 = 16, M8 = 28),
and `_NM` is retained. `execMask_M5` checks the offset, `masked_mov_decodes`
shows that a real `(M5, 16)` move keeps its mask, and `parseExec_rejects_M9`
keeps the mask range closed. The vector-add decoder now accepts all six M5
moves; the remaining twelve refusals are the predicate `cmp`/`and`/`or` forms
and the two predicated `goto`s.

This stage is decoding only: `stepWith` still uses the execution size and does
not yet apply the mask offset to lane selection or partial-register writes.

## Stage 93: predicate `and` and `or`

The two predicate-logic forms in the vector-add loop now decode and execute:

```lean
theorem predAnd_lane : (stepWith ... (.predAnd e p a b)).preds p l =
  (s.preds a l && s.preds b l)
theorem predOr_lane  : (stepWith ... (.predOr e p a b)).preds p l =
  (s.preds a l || s.preds b l)
```

Both write only active lanes, preserve other predicates and preserve inactive
lanes; the six frame/lane theorems are in the axiom audit. The vector-add
decoder now accepts 33 of 41 instructions. The remaining eight refusals are the
four register `cmp.lt`s, two `cmp.eq`s and two predicated `goto`s.

## Stage 94: register comparisons

The vector-add loop's comparisons test two GRF regions rather than an
immediate. `cmpLtReg` and `cmpEqReg` decode and compare the low 32 bits per
lane, writing the destination predicate only on active lanes. `cmpLtReg_lane`,
`cmpEqReg_lane` and their predicate/lane frame lemmas are in the audit.

The decoder now accepts 39 of 41 vector-add instructions; only the two
predicated `goto`s remain.

## Stage 95: predicated gotos decoded

The predicated-branch mnemonic now parses any predicate and both polarities:
the literal `(!P1) goto` special case became `parsePredGoto`, with
`predicated_gotos_decode` checking the real `(!P3)` and `(!P6)` forms. All 41
vector-add instructions (46 statements including five labels) decode.

Control flow is still the documented uniform model: `runRealCF` reads lane 0.
This stage closes decoding, not divergent branch execution; per-lane branch
masks and re-convergence remain open.

## Stage 96: masked moves

Masked moves now have their own instruction, `movMasked`, rather than sharing
the total-write `mov` semantics. `writeMaskedWith` uses the mask's channel
offset and preserves destination elements outside the active window;
`srcIndexRegion` includes the source region's vertical and horizontal stride.

```lean
theorem maskedMov_unit_lane : (stepWith ... (.movMasked e dst src)).regs
  (alias dst.num) (dst.dstIndex (e.laneIndex l)) =
  readSrcIndexed alias s src (e.laneIndex l)   -- when lane l is active
```

The theorem is scoped to unit-stride destinations. The real dump also has two
stride-two destinations (`V0081(2,0)<2>` and `V0081(2,1)<2>`); their write
logic is present but their lane law is the next refinement. Other instructions
still use their pre-mask semantics, so this is the first partial execution of
`(M5, 16)`, not a complete SIMD mask model.

## Stage 97: stride-two masked destinations

`maskedMov_stride2_lane` closes the destination-shape gap:

```lean
theorem maskedMov_stride2_lane : (stepWith ... (.movMasked e dst src)).regs
  (alias dst.num) (dst.dstIndex (e.laneIndex l)) =
  readSrcIndexed alias s src (e.laneIndex l)   -- when dst.hstride = 2
```

An active lane writes `base + 2 * (lane - maskOffset)`, matching the real
`V0081(2,0)<2>` / `V0081(2,1)<2>` forms. The write helper already supported
this layout; the stage supplies the checked lane law. Masked execution is now
covered for all six real M5 moves. General mask application outside moves and
the loop effect remain open.

## Stage 98: masked-move frames and a negative mask test

The masked-move laws now compose:

```lean
theorem maskedMov_frame     : preds, mem and halted are unchanged
theorem maskedMov_other_reg : every other register is unchanged
theorem mask_offset_load_bearing :
  lane 0 is inactive under M5, lane 16 is active, but lane 16 is inactive if
  the same instruction is read as M1
```

The last theorem is the negative test for stage 92: a decoder that dropped the
mask would still pass syntax checks but would activate the wrong lane set.

## Stage 99: packed DPAS operands

The real FMHA instruction's operands are now given their ISA layouts:

- A (`r39:hf8`) and C (`r383:f`) are row-major register-file data;
- B (`r335.0:hf8`) is column-packed, with depth `k` in byte `k % 4` of dword
  `n` in GRF `k / 4` after the base;
- `fmhaRealPackedAtom_correct` connects those packed operands to
  `fmhaAtom_correct`;
- `fmhaRealB_address` checks one concrete B address.

The GRF width is parameterised (8 or 16 dwords); the real instance uses 16.
This models the documented layout, while the compiler's choice of operand
bases remains transcribed from the dump.

## Stage 100: packed addresses are collision-free

The layout maps are explicit and proved injective over their valid ranges:

```lean
theorem fmhaBAddr_injective    : distinct (k, n) -> distinct B addresses
theorem fmhaAAddr_injective16  : k < 32 -> distinct A addresses
theorem fmhaCAddr_injective16  : n < 8 -> distinct C addresses
```

Thus two different logical A, B or C elements cannot alias the same register
byte in the modelled 16-dword layout. This is a property of the layout, not a
statement about the compiler's chosen operands or values.

## Stage 101: DPAS register bases from the dump

`parseDpasRegs` reads the register number and optional subregister from each
DPAS operand. `realFmhaDpas_regs` proves the real line decodes to
`C = r383, B = r335.0, A = r39`, and
`fmhaReal_uses_decoded_bases` proves those are exactly the bases used by the
packed layout. The operand bases are no longer bare numbers in the packing
module; they are tied back to the instruction text.

## Stage 102: a packed DPAS known-answer test

`fmhaRealPackedAtom_ones` executes the modelled atom on a concrete register
file whose packed A and B bytes are all one and whose C region is zero. The
32-deep fp8 dot yields exactly 32:

```lean
theorem fmhaRealPackedAtom_ones :
  fmhaAtom (fmhaRealA fmhaOnesRegs) (fmhaRealB fmhaOnesRegs)
    (fmhaRealC fmhaOnesRegs) 0 0 0 0 = 32
```

The proof rewrites with `fmhaRealPackedAtom_correct` and kernel-evaluates the
32-step accumulation. This is a model-level smoke test for the packing and
atom, not a hardware conformance run.

## Stage 103: destination regions use `<hstride>`

The parser had been reading every one-field region as the source shorthand
`<vstride;1,0>`. For a destination, the field is a horizontal stride:

```
mov (M5, 16) V0081(2,0)<2> V0082(1,0)<1;1,0>
```

must decode to destination `row = 2, vstride = 1, hstride = 2`, not
`vstride = 2, hstride = 0`. `parseDstGrf` now handles destinations separately;
`masked_stride2_decodes` pins the real form, and all explicit instruction lists
were updated. `Grf.dstSimple` now means a unit-stride destination.

This was a real correctness bug: the old decoded M5 stride-two moves would
have fallen through the masked-write helper without writing their destination.

## Stage 104: the loop vector add's real tables and index

The original dump behind `Intel/Examples/RealVectorAdd.lean` was located
locally, including its `.decl` table. `Intel/VectorAddLoop.lean` now transcribes
the aliases, register types and element counts and proves the exact preamble:

```lean
theorem vaLoopPreamble_id :
  (runVAL s vaLoopPreamble).regs 59 l =
    zext localSize * zext r0 + (localId l).zeroExtend 64 + zext globalOffset
```

The result is the real 64-bit loop index. `vaLoopPreamble_mem` shows the
preamble changes registers only.

This also exposes the next model boundary: `V0059` is a qword-per-lane
register and `V0061` is its dword view. The current `RealState` stores one
64-bit slot per element and models register-number aliases, not bitwise
dword/qword views, so the pack/select loop body still needs a dword-level
register model before its effect can be claimed.

## Stage 105: dword storage and qword views

`Intel/DwordView.lean` supplies the missing storage layer:

```lean
abbrev DRegs := Nat → Word
def qwordOf (r : DRegs) (i : Nat) : Addr
def setQword (r : DRegs) (i : Nat) (v : Addr) : DRegs
```

It proves dword write/read laws, that `setQword` splits into low and high
dwords, that the qword round trip is exact (`qwordOf_setQword`), and that
writing an unrelated dword preserves the qword. This is the foundation needed
to model `V0061` as a dword view over the qword-per-lane `V0059`.

## Stage 106: the real loop body's memory effect

`Intel/VectorAddLoopBody.lean` proves the exact four instructions at
`_0_009`:

```lean
theorem vaLoopBody_store_at :
  (runVAL s vaLoopBody).mem (cPtr.toNat / 4 + idx l) =
    s.mem (aPtr.toNat / 4 + idx l) + s.mem (bPtr.toNat / 4 + idx l)
```

`realVectorAdd_body_prefix` checks the decoded prefix, `vaLoopBody_sum`
proves the add result, and `vaLoopBody_mem` gives the store-vector form. The
proofs use the real pointer/index aliases and the per-lane 64-bit index.

This is one loop-body memory step, not the whole loop: the qword/dword
pack/select update of `V0059` remains the next stage.

## Stage 107: the 24-lane pack layout

The native assembly resolves the M5 destination question:

```
mov (16|M0)  r20.0<1>:d  r15.0<2;1,0>:d
mov (16|M16) r21.0<1>:d  r17.0<2;1,0>:d
```

The M5 destination is the relative row window (`r21.0`, dwords 8..23), not a
channel-shifted out-of-range address. The overlap dwords 8..15 receive the
same values, so the combined two-move result is `dst[j] = src[2*j]` for
`j < 24`. The same pattern holds for the odd-dword high half and the final
writeback into `V0059`.

`Intel/LoopPack.lean` formalizes this as `packEven24`, `packOdd24` and
`writeId24`, proving the 24-lane values and the qword writeback
(`writeId24_qword`). This is the pack/writeback layout; composing it with the
actual `sel`/branch instructions remains.

## Stage 108: loop-carried ID selection

The continuation decision is now expressed as a per-lane selection:

```lean
def selectId (old new : Nat → Addr) (takeNew : Nat → Bool) : Nat → Addr :=
  fun l => if takeNew l then new l else old l

theorem writeId24_selected_qword :
  qwordOf (writeId24 r (low of selected) (high of selected)) l =
    selectId old new takeNew l
```

The low/high pack and writeback reconstruct the selected 64-bit index exactly
for every active lane. This isolates the data-update law from the remaining
instruction-level `sel` and branch composition.

## Stage 109: end-to-end loop-body effect

The real index preamble and the real load/add/store body are composed:

```lean
theorem realVectorAdd_loop_effect :
  (runVAL (runVAL s vaLoopPreamble) vaLoopBody).mem
    (cPtr / 4 + id l) = s.mem (aPtr / 4 + id l) + s.mem (bPtr / 4 + id l)
```

for an active lane `l < 24`, where `id l` is the exact 64-bit index computed by
the preamble. `vaLoopPreamble_frame` records that the preamble preserves the
three pointers and memory, and `vaLoopPreamble_bodyPre` builds the body
precondition.

For this range kernel the index stride is `globalSize`, so after one body
`id + globalSize ≥ globalSize`; the next continuation test is false and the
loop exits. The instruction-level branch/termination proof is the remaining
step; the per-lane output effect itself is now proved.

## Stage 110: loop termination arithmetic

`vaLoopNext_not_lt` proves that after adding `globalSize` (with no 64-bit
overflow) the next index cannot satisfy `next < globalSize`. Thus this range
kernel executes at most one body per lane. The result is the arithmetic side
of termination; the remaining work is to connect it to the decoded predicated
branch sequence.

## Stage 111: global-size guard

`VaLoopSizePre` records the two dwords of the 64-bit global size.
`vaLoopPreamble_size` proves the preamble copies them into `V0049`; the loop
uses `V0065` as their alias. `vaLoopSize` assembles the 64-bit value,
`vaLoopGuard` is the continuation predicate, and `vaLoopNext_guard_false`
proves the guard is false after one stride. This connects the size constant to
the termination arithmetic; the decoded compare/branch sequence remains.

## Stage 112: per-lane control flow

`runRealCFLaneWith` extends the control-flow interpreter with an explicit lane:
`gotoIf` reads that lane's predicate instead of the uniform lane-0 bit.
`runRealCFLaneWith_zero` proves it agrees with the existing interpreter at lane
0, and `runRealCFLane_gotoIf_taken` / `_not_taken` expose the two branch cases.

This is the control-flow piece needed to connect the loop guard and
termination facts to the decoded `sel`/branch sequence without assuming
uniformity across all lanes.

## Stage 113: the decoded loop and its real branch sites

`Intel/VectorAddLoopProgram.lean` materializes all 46 decoded statements and
proves `realVectorAdd_decoded_eq`. It exposes the exact label indices and both
real predicated branch sites:

```lean
theorem vaLoop_first_body  : P3 lane = true  -> pc 17 falls through to 18
theorem vaLoop_first_exit  : P3 lane = false -> pc 17 jumps to 44
theorem vaLoop_second_select : P6 lane = true  -> pc 35 falls through to 36
theorem vaLoop_second_exit   : P6 lane = false -> pc 35 jumps to 44
```

These are the decoded per-lane branch paths. The remaining composition is to
show the predicates are the proved guard/termination values.

## Stage 114: the first guard predicate

`Intel/LoopGuard.lean` proves that the five instructions at PCs 12-16 compute
the 64-bit guard from the packed low/high halves:

```lean
theorem vaLoopP3_guard :
  (runVAL s vaGuardBlock).preds 3 lane =
    vaLoopGuard (vaLoopSize lo hi) (vaLoopSize sizeLo sizeHi)
```

The proof reduces the compare/and/compare/or sequence and uses a bitvector
lemma equating the lexicographic low/high comparison with the assembled
64-bit comparison. The remaining connection is to derive the low/high
register facts from the pack moves.

## Stage 115: the second guard predicate

`vaGuardBlock2` covers the symmetric five instructions at PCs 30-34.
`vaLoopP6` and `vaLoopP6_guard` prove that the second continuation predicate
is the same lexicographic/64-bit guard, now from the increment's packed halves
in `V0075`/`V0076`. Both real guard blocks are therefore covered.

## Stage 116: packed halves of a qword ID array

`idDwords` is the dword view of a qword-per-lane ID array. `packLow_dword` and
`packHigh_dword` prove the 24-lane even/odd packs select exactly the low and
high dwords of each qword. This connects the pack layout to the register-halves
premises used by the guard predicates.

## Stage 117: the native M1/M5 windows

`m1Pack` and `m5Pack` encode the two native move windows. `m5_m1_even` and
`m5_m1_odd` prove the M5 row-1 move overwrites the overlap with identical
values, so the pair is exactly the 24-lane even/odd pack. This closes the
move-window dataflow at the dword-model level.

## Stage 118: the loop's dword-view step

`stepLoop` gives `mov`/`movMasked` the correct dword view for the two packed
source registers `V0061` and `V0074`; other instructions delegate to the
unified `stepVAL`. `stepLoop_mov61_unit` and `stepLoop_mov74_unit` prove the
active-lane destination value for both dword-view sources.

This bridges the dword-pack model to an executable step over the real program.

## Stage 119: masked dword-view moves

`writeMaskedWith_other_reg` proves a masked write cannot disturb another
register. `stepLoop_movMasked61_unit` and `stepLoop_movMasked74_unit` extend the
dword-view lane laws to the masked move form used by the M5 pack. These are
the lemmas needed to compose the actual two-move pack.

## Stage 120: executing the real low pack

`vaPackLow_value` executes the actual M1+M5 low pack through `stepLoop`:

```lean
theorem vaPackLow_value :
  low32 ((runRealWith stepLoop s vaPackLow).regs 62 j) =
    (ids j).truncate 32   -- for j < 24, when V0059 holds ids
```

This proves the real two-instruction sequence produces the low halves used by
the first guard comparison.

## Stage 121: executing the real high pack

`vaPackHigh_value` is the high-half counterpart:

```lean
theorem vaPackHigh_value :
  low32 ((runRealWith stepLoop s vaPackHigh).regs 63 j) =
    ((ids j) >>> 32).truncate 32   -- for j < 24
```

Both real M1+M5 packs now execute through the dword-view step and produce the
register halves consumed by the guard comparisons.

## Stage 122: both packs in one state

`vaPackBoth_value` composes the low and high packs:

```lean
theorem vaPackBoth_value :
  low32 result.regs 62 j = (ids j).truncate 32 ∧
  low32 result.regs 63 j = ((ids j) >>> 32).truncate 32
```

The proof also shows the high pack preserves `V0062` and the low pack
preserves `V0059`, so both halves remain valid after sequential execution.

## Stage 123: the first guard from executed packs

`vaLoopP3_packed` instantiates the guard theorem with the executed low/high
packs. For every active lane it yields

```lean
theorem vaLoopP3_packed :
  P3 = vaLoopGuard (ids j) (vaLoopSize sizeLo sizeHi)
```

from the packed register halves and the two size-dword facts. The remaining
work is proving those size-register facts survive the packs.

## Stage 124: P3 with preserved size dwords

The four pack moves preserve `V0049`, and `vaPackBoth_preserves49` lifts that
to the composed pack. `vaLoopP3_packed_full` uses those facts to derive
`P3 = id < globalSize` directly from the launch size dwords, with no remaining
size assumption about the post-pack state.

## Stage 125: the increment's low pack

`vaPackIncLow_value` executes the M1+M5 low pack from `V0074` into `V0075`
through `stepLoop`, proving the register contains the low dwords of the next
IDs for lanes 0..23.

## Stage 126: the increment's high pack

`vaPackIncHigh_value` is the high-half counterpart: the M1+M5 moves from
`V0074` into `V0076` produce the high dwords of the next IDs for lanes 0..23.

## Stage 127: both increment packs

`vaPackIncBoth_value` composes the increment low/high packs and proves
`V0075`/`V0076` simultaneously contain the next ID halves. The high pack
preserves `V0075`, and the low pack preserves the `V0074` source register.

## Stage 128: increment packs preserve the size dwords

`vaPackIncBoth_preserves49` proves all four increment-pack moves leave
`V0049` untouched; `vaPackIncBoth_preserves49_low32` exposes the form used by
the second guard. The P6 path therefore does not need a post-pack size
assumption.

## Stage 129: full P6 from executed increment packs

`vaLoopP6_packed_full` composes the executed increment packs, preserved size
dwords and the second guard:

```lean
theorem vaLoopP6_packed_full :
  P6 = vaLoopGuard nextId globalSize
```

Both continuation predicates are now derived from the actual executed packs
and launch size facts.

## Stage 130: decoded branch composition

`Intel/LoopControl.lean` composes the decoded branch sites with the proved
guard values:

- `vaLoopP3_branch_exit` / `_fallthrough` at PC 17;
- `vaLoopP6_branch_exit` / `_fallthrough` at PC 35;
- `vaLoop_branch_paths` packages both decisions.

## Stage 131: the increment add

At PC 25, `vaLoopIncAdd_value` proves the loop computes
`V0072[l] = V0059[l] + V0067[0]`, the next ID per lane, and
`vaLoopIncAdd_preserves49` keeps the size dwords available for P6.

## Stage 132: executing the decoded P3 prefix

`Intel/LoopP3Exec.lean` proves the decoded PC 8..16 slice is exactly the pack
plus first guard and that running it sets `P3` to the proved guard on every
active lane.

## Stage 133: executing the decoded P6 prefix

`Intel/LoopP6Exec.lean` proves the decoded PC 26..34 slice is exactly the
increment packs plus second guard and that running it sets `P6` to the proved
next-ID guard.

## Stage 134: executing the decoded body slice

`Intel/LoopBodyExec.lean` proves PC 21..24 is exactly `vaLoopBody` and that
`stepLoop` agrees with `stepVAL` there, transferring the proved
`C[index] = A[index] + B[index]` effect to the actual decoded slice.

## Stage 135: executing the decoded entry slice

`Intel/LoopEntryExec.lean` proves the decoded PCs 18--20 are the two labels
and the stride move, preserving memory, predicates and `V0059` while writing
`V0067[0]` from `V0068`/`V0037`.

## Stage 136: per-lane end-to-end control path

`Intel/LoopEndToEnd.lean` composes the decoded entry, body, increment and
second-guard slices with the per-lane interpreter. `vaLoop_lane_body_exit`
proves that a lane entering at PC 17 with `P3 = true` reaches the exit branch
at PC 44 when `P6 = false`; `vaLoopP6_false_of_range` derives that exit from
the range-completion fact.

The body's store effect is proved in `Intel/LoopBodyExec.lean`, but transporting
it through the remaining slices is still open.

## Stage 137: per-lane memory effect on the decoded path

`Intel/LoopMemoryTransport.lean` proves the post-body increment/guard slices
preserve memory, transports the entry state into `VaLoopBodyPre`, and connects
the decoded body store to the full path. `vaLoop_lane_body_exit_mem` and
`vaLoop_lane_body_exit_with_guard_mem` state the resulting
`C[id] = A[id] + B[id]` effect on the PC 44 target state.

## Stage 138: deriving the path guards from the decoded prefix

`Intel/LoopGuardPath.lean` removes the abstract `P3`/`P6` hypotheses from the
stage-137 path. `vaLoopCFP3` executes the nine decoded instructions at PC 8--16
and lands at PC 17. `vaLoopP3Prefix_preserves_reg` and
`vaLoopBodySlice_preserves_reg` are the prefix/body frames, `vaLoopPreP6_regs72`
computes the pre-guard index as `V59 + V37`, and `vaLoopPreP6_preserves49`
keeps the bound registers intact. `vaLoop_lane_body_exit_pc8_mem` then starts
at PC 8 and needs only the real P3 guard, the range bound, and the body's
memory-safety hypotheses.

## Stage 139: per-location visibility and release/acquire

`Intel/MemoryVisibility.lean` adds a small memory model: each location has a
store log with a visible prefix, plain writes stay pending, a release fence
publishes the whole log, and an acquire fence is identity in the cacheless
model. `read_write_same`, `write_write_order` and `read_never_unwritten` state
the coherence laws; `release_acquire_message_passing` proves that observing a
released flag returns the published data, and `without_release_stale_observable`
shows the release is load-bearing. The module docstring lists the model
assumptions and the parts that remain outside it.

## Stage 140: the decoded kernel entry from PC 0

`Intel/LoopKernelEntry.lean` runs the eight decoded instructions at PC 0--7
(the label, the prologue and the six index operations) and proves the register
facts needed at PC 8: the size dwords, the per-lane index and the pointer
frames. `vaLoop_kernel_pc0_mem` composes those facts with stage 138, so the
kernel's `C[id] = A[id] + B[id]` effect now starts at PC 0 with the launch
registers, the size constant and the three pointers.

## Stage 141: generic execution-mask laws

`Intel/MaskExec.lean` supplies the reusable laws behind masked execution:
`Exec.laneActive_not_noMask` and `Exec.laneActive_noMask` characterize the
active window, `Exec.laneIndex_lt_size` and `Exec.laneIndex_injective_on_active`
cover operand indices, and `writeMaskedWith_unit_coverage` states that a
unit-stride masked write touches exactly the destination images of its active
lanes and fixes every other element. `writeMaskedWith_commute_unit` gives the
footprint condition under which two masked writes commute, and the `_NM` laws
record that `_NM` means "no channel mask" rather than an empty mask.

## Stage 142: FMHA atom value refinement and tile composition

`Intel/FmhaAtomTile.lean` refines the coded FMHA 8x8x32 atom at the value
level. `fmhaAtom_eq_slab` and `fmhaAtom_eq_dpas` identify it with one depth-32
`dpas` at the same origin, `fmhaAtom_eq_sum_halves` and `fmhaAtom_eq_two_dpas`
split that step into two K=16 halves, and the `fmhaGrid2x1`/`fmhaGrid2x2`
lemmas show that atoms over disjoint 8x8 accumulator blocks compose into the
pointwise sum of their depth-32 deltas. The fp8 element encoding remains the
assumption recorded in `Intel.RealDpas`.

## Stage 143: predicated lanes write nothing

`Intel/LoopKernelInactive.lean` covers the false side of the decoded `gotoIf`
at PC 17. `vaLoopP3Prefix_mem` shows the pack/guard prefix is memory-only
neutral, and `vaLoop_lane_inactive_mem` proves that a lane whose real P3 guard
is false runs from PC 0 to the PC 44 exit with memory exactly unchanged. No
pointer or aliasing hypothesis is needed: the lane never reaches the body.

## Stage 144: reaching `ret`

`Intel/LoopKernelExit.lean` runs the PC 44 exit label and the decoded `ret`.
`vaLoopCFLane_exit_halted` proves the halt flag, `vaLoop_pc8_exit_halted`
carries that through the PC 8 path, and `vaLoop_kernel_pc0_effect` combines
the halt with the stage-140 memory effect: from PC 0, an active lane halts at
`ret` with `C[id] = A[id] + B[id]`.

## Stage 145: global/SLM disjointness and workgroup barriers

`Intel/SlmAliasing.lean` refines the immediate-visibility SLM model with the
stage-139 visibility model. `MixedState` keeps global and workgroup-private SLM
in separate address spaces, so `gstore_slm_frame`, `sstore_global_frame`,
`sload_gstore` and `gload_sstore` give the aliasing frames. A workgroup barrier
is a full release/acquire fence: `wgBarrier_slmInvariant` publishes every
pre-barrier SLM log, `sload_wgBarrier_sstore` reads the stored tile back, and
the producer/consumer theorems include a negative test showing the barrier is
load-bearing.

## Stage 146: grid-stride indices and store composition

`Intel/GridStride.lean` isolates the value-level grid-stride loop.
`strideId start stride k = start + k * stride`, `strideId_guard_true_before`
and `strideId_guard_false_at_bound` give the two guard sides under the exact
in-range boundary, and `strideId_pairwise_distinct` proves positive strides
produce distinct addresses under the no-wrap bound. `gridStore_correct`
composes `C[id_k] = A[id_k] + B[id_k]` over `n` iterations and keeps every
other word at its initial value. The module notes the literal "`start < size`
implies all `k < n` are in range" statement is false and uses the correct
boundary instead.

## Stage 147: SBID fields in an encoded SEND descriptor

`Intel/SbidEncoding.lean` makes the abstract `Token := Nat` of the SEND model
concrete. It documents one transcribed descriptor layout (SBID at bits
`[8, 16)`), defines `sbidOf`/`mkDesc`, and proves `sbidOf_mk`,
`distinct_sbids_distinct_tokens`, the two-SBID pending/all-done progression,
and that waiting on or committing one token does not consume the other.
`loadPipelineSbid_value` reuses the pipeline facts on an encoded descriptor.
Out-of-range SBID fields are rejected. The layout is a model assumption, not
a binary reading: the dumps do not print SBIDs.

## Stage 148: fp8 E4M3 decode for the FMHA atom

`Intel/Fp8Decode.lean` models the low-precision element path of the coded FMHA
atom. It decodes E4M3FN (bias 7, subnormals, `S.1111.111` as NaN, no infinity)
into an exact fixed-point value, proves the exact values of `1.0`, `1.5`,
`2.0`, `0.5`, zero, the minimum subnormal and the maximum finite, and defines
`fmhaAtomFp8` over fp8 tiles. `fmhaAtomFp8_eq_fmhaAtom` connects it to the
existing atom when every read element is non-NaN, and the concrete all-ones and
unit-tile theorems check the 32-term atom by computation.

## Stage 149: IEEE fp16 addition rounding

`Intel/IeeeFp16Add.lean` proves a restricted IEEE-754 fp16 addition result.
`fp16_add_single_rounding` states that an exact-grid sum needs no rounding;
`fp16_add_halfway_even` and `fp16_add_halfway_even_mantissa` prove the
tie-to-even rule; and `fp16_add_no_double_rounding` proves that the
decode/add/encode path performs exactly one rounding. The module also records
that a general nested-rounding identity is false
(`double_rounding_counterexample`) and documents the proved class: normalized
finite operands, a supplied destination exponent, no subnormals, signed zeros,
NaN payloads, overflow to infinity or FMA. It is not a full IEEE FMA.

## Stage 150: register-level FMHA DPAS execution

`Intel/FmhaExec.lean` executes the decoded FMHA DPAS on a register file.
`fmhaDpasStep_c` / `fmhaDpasStep_atom` show the C block at the decoded base is
`fmhaAtom` over the register-file tiles, `fmhaDpasStep_frame` fixes everything
outside the C block, and `fmhaDpasStep_decoded` specializes to the decoded
`⟨383, 335, 0, 39⟩` bases. The two-atom theorems on C bases 383 and 391 show
disjoint updates commute and sum pointwise. The logical tile addressing is a
documented model assumption; the dump gives bases, not the full physical
layout.

## Stage 151: mask-aware execution for the loop body

`Intel/MaskedBody.lean` gives non-mov instructions their execution masks.
`stepMasked` applies `Exec.laneActive`/`Exec.laneIndex` to `add`, `add3`,
loads and stores: inactive destination lanes keep their prior values and
inactive store lanes emit no write. `stepMasked_*_reg_full` and the store
agreement lemmas show that full 32-lane controls reproduce `stepWith`, and the
`vaLoopBody_runMasked_*` theorems transfer the body's
`C[id] = A[id] + B[id]` effect to the masked semantics. The module also
records the footprint caveats: an inactive-store frame needs address
disjointness, and offset masks compress destinations by lane index.

## Stage 152: cross-lane race freedom

`Intel/KernelRaceFree.lean` proves that the kernel's lane writes are disjoint
when the launch ids are distinct. `vaLoopId_injective` and
`vaLoopId_pairwise_distinct` follow from `BitVec` addition cancellation,
`vaLoopKernel_cAddress_ne` and `vaLoopKernel_writes_disjoint` give the C-word
addresses, and `vaLoop_kernel_pc0_mem_of_laneDistinct` discharges the stage-140
`hdistinct` hypothesis from lane injectivity. The counterexample theorems show
that injectivity is load-bearing: a constant `localId` makes two lanes alias.

## Stage 153: composing the 32 lane stores

`Intel/WorkgroupEffect.lean` composes the per-lane stores into one workgroup
result. `laneStoresAt_correct` proves that after applying one
`C[id] = A[id] + B[id]` store per id, every written word holds its sum and
every other word keeps its initial value. `laneIds_nodup` derives the required
duplicate-freedom from launch-id injectivity, and `vaLoop_workgroup_correct`
instantiates the result to the 32 `vaLoopId` lanes. This is the observable
workgroup memory once race freedom (stage 152) is known, not a new concurrent
semantics.

## Stage 154: write-through cache coherence

`Intel/CacheCoherence.lean` adds one workgroup cache over the visibility model.
`CacheState` pairs the shared `VisState` with per-location cache lines;
`load` hits the cache or fills from global, `store` is write-through,
`invalidate` drops lines, and `flush`/release fences publish pending writes.
`load_store_same`, `invalidate_load_global` and `flush_publishes` are the core
laws; `cache_message_passing` proves the producer/consumer pattern with
invalidate, and the negative test shows a stale line is observable without it.
The docstring lists the assumptions: write-through, no write-allocate, one
cache per workgroup, no coherence traffic, full-barrier fences.

## Stage 155: register-level FMHA mainloop

`Intel/FmhaMainloop.lean` iterates stage 150's DPAS step over T depth slabs.
`fmhaMainloopStepAt_zero` and `_succ` are the recurrence,
`fmhaMainloopStepAt_c` states the C-block result as `dpasRun`,
`fmhaMainloopStepAt_c_dotMat` gives the K = T*32 dot product, and
`fmhaMainloopStepAt_frame` fixes everything outside the C block. The T=2
specializations match the two-atom and K=16-half decompositions, and the pair
theorems show disjoint C blocks compose. The logical packing is the same model
assumption as stage 150; tail/partial K and hardware layout remain open.

## Stage 156: fp16 special values and overflow

`Intel/IeeeFp16Special.lean` extends stage 149 to the special-value cases.
`decodeFull` covers all 65536 words (finite subnormals at `2^-24`, distinct
signed zeros, tagged NaN/Inf), and `decodeFull_of_decode` agrees with the
normalized decoder. The module proves signed-zero rules, exact subnormal and
subnormal-to-normal crossings, ties-to-even bit examples, the exact overflow
threshold `65520`, NaN/Inf propagation with a documented left-NaN payload
convention, and counterexamples showing flush-to-zero and verbatim sNaN
preservation are not IEEE behavior. It is still not a full IEEE FMA: general
round-to-nearest for every binade, exception flags and fused multiply-add
remain outside it.

## Stage 157: coherence traffic between two caches

`Intel/CacheTraffic.lean` models two workgroup caches over one shared
visibility state. `TwoCache` has producer and consumer caches;
`writeThroughBroadcast` stores and synchronously invalidates the other cache,
and `TwoCacheCoherent` states that every valid line equals the visible global
value. `producer_write_broadcast_consumer_observes` proves the fresh read, the
negative tests show the stale line without the broadcast, and
`producerPublishBroadcast_message_passing` covers the data-then-flag pattern.
Assumptions: write-through, no write-allocate, one line per address per cache,
synchronous broadcast invalidation, no directory/ownership protocol or relaxed
atomics.

## Stage 158: the decoded loop-back block

`Intel/LoopGridStrideControl.lean` executes PCs 36--43: the `_0_010` label,
the two `sel` instructions and the four 16-lane writeback packs, then the
`goto` back to `_0_009` at PC 20. `vaLoop_loopBack_id` proves the qword view of
`V0059` becomes `selectId old (old + stride) takeNew` for lanes below 24, and
`vaLoop_loopBack_is_strideId` identifies this as one `strideId` step.
`vaLoop_lane_second_body` proves the intended second-iteration store on the
value-level reentry state.

The module also records an open modeling gap: after the decoded dword-view
writeback, `regs 59 l` for `l < 24` holds dword slot `l`, while the PC 21 load
reads `regs 59 l` as a qword lane. `vaLoopLoopBack_dword_counterexample`
proves the naive all-lane reconstruction is false, so a fully literal second
iteration needs a dword/qword coalescing step in the existing semantics.

## Stage 159: directed fp16 rounding

`Intel/IeeeFp16Directed.lean` adds round-toward-zero, round-down and round-up
for the fp16 value model. It proves the directed bounds, exact-grid fixed
points, that ties-to-even always lies between down and up, and subnormal /
first-normal-binade results under every mode. The overflow table is exact:
toward zero saturates at signed `65504`, up-positive and down-negative go to
infinity above `65504`, and the other directions saturate. Bit-level examples
and counterexamples show where the modes differ. General per-binade RNE,
exception flags and FMA remain open.

## Stage 160: dword/qword coalescing adapter

`Intel/DwordCoalesce.lean` supplies the adapter for the stage-158 gap.
`coalesceDword` merges the two dword slots of a qword lane, `coalesceReg59`
rewrites only `V0059`, and `coalesce_writeback` proves the coalesced loop-back
value is `selectId old (old + stride) takeNew` for `l < 24`.
`coalesced_bodyPre` gives the body preconditions and
`vaLoop_lane_second_body_literal` proves the literal second-iteration store
`C[idx] = A[idx] + B[idx]`. The raw model still has the dword/qword gap
(`coalesce_raw_counterexample`); coalescing is the explicit hardware
interpretation.

## Stage 161: n-iteration grid-stride induction

`Intel/LoopMultiIteration.lean` lifts stage 160 to `n` iterations.
`vaLoop_coalesced_iteration_step` is the exact PC 21 to PC 21 iteration with
coalesced re-entry and `id + stride`; `vaLoop_coalesced_iteration` is the
guard-shaped induction concluding index `strideId id stride n` and every prior
`C[id_k] = A[id_k] + B[id_k]`, under `VaLoopIterMemorySafe`;
`vaLoop_coalesced_iteration_two_literal` matches stage 160, and
`vaLoop_coalesced_iteration_branch`/`_exit` connect the loop to the stage-136
exit. The lane bound remains `l < 24`; lanes 24--31 keep the raw dword slots.

## Stage 162: directory/ownership coherence

`Intel/CacheDirectory.lean` adds a synchronous directory with per-location
ownership and sharer sets. `readRequest` shares a line, `writeRequest` and
`writeWithOwnership` acquire exclusive ownership and invalidate sharers, and
`DirectoryInvariant` states owner uniqueness, read-only sharers and fresh valid
lines. `writeWithOwnership_invalidates_sharers`, `readAfterWrite_fresh` and
`no_stale_after_ownership_transfer` are the core laws;
`writeWithOwnership_message_passing` covers data-then-flag. Negative tests show
a write without ownership transfer and a read that ignores the directory can
both observe stale data. Request queues, write-back dirty lines and relaxed
atomics remain outside the model.

## Stage 163: FMHA tail and partial K

`Intel/FmhaTail.lean` models `K = T*32 + r` with `0 < r < 32` by zero-padding
the operand depth beyond `K`. `tailSlab_eq_dotMatFrom` proves the padded tail
slab equals the partial dot product over `[T*32, T*32+r)`, and
`fmhaMainloopTail_c` gives the T full slabs plus tail as `C + dotMat ... K`.
The `r = 0` and `T = 0` specializations reduce to stage 155 and to a short K;
the frame law fixes everything outside C. Zero-padding is a value-level
idealization; masked/partial DPAS hardware behavior is not modeled.

## Stage 164: general fp16 round-to-nearest-even

`Intel/IeeeFp16GeneralRne.lean` selects the destination binade for a finite
exact sum (`destExp`, `destQuantum`, `destMant`), proves the quantum bounds and
that `roundScaled` is IEEE round-to-nearest-even at that quantum with
ties-to-even inherited from `roundEvenNat`. `addGeneral_fin` covers every
finite exact sum below the stage-156 overflow threshold, across all subnormal
and normal binades through exponent 30, and agrees with `addFull` on the
previously covered classes. The overflow branch stays with stage 156;
exception flags and FMA remain outside the model.

## Stage 166: fp exception flags

`Intel/FpExceptionFlags.lean` adds a sticky flag set (`invalid`, `divByZero`,
`overflow`, `underflow`, `inexact`) with union algebra and fold monotonicity.
`addFlags` classifies fp16 addition: NaN operands and opposite infinities are
invalid, at/above the stage-156 threshold is overflow, a rounded value that
differs from the exact sum is inexact, and underflow is tiny-after-rounding
plus inexact. `addFlags_exact_none`, `addFlags_inexact_iff`,
`addFlags_overflow` and the invalid cases are proved.
`finAddFlags_underflow_false` shows a decoded fp16 addition never raises
underflow (tiny sums are exact on the `2^-24` grid); a finer-grid witness
exercises the rule. Hardware traps, sticky lane state and FTZ/DAZ are not
modeled.

## Stage 167: relaxed atomics and store buffers

`Intel/RelaxedAtomics.lean` models `relaxed`, `release`, `acquire`, `acqRel`
and `seqCst` over a per-location store buffer. `later_store_observed_earlier_
pending` and `relaxed_message_passing_stale` show the relaxed reordering gap;
`releaseAcquire_message_passing` and `releaseAcquire_no_stale` prove the
release/acquire invariant; `seqCstProgram_eq_releaseAcquireProgram` and
`seqCst_outcomes_subset_releaseAcquire` state the seq_cst relation. Fences
drain the buffer (`sbReleaseFence_published`, `sbReleaseFence_idem`), and
visibility is monotone. Assumptions: per-location FIFO, cacheless global
memory, no store-to-load forwarding, fences as full barriers.

## Stage 168: write-back caches and request queues

`Intel/CacheWriteBack.lean` adds dirty lines, eviction and FIFO request queues.
`writeBack` marks a line dirty, `evict`/`flushLine`/`flushAll` publish it, and
`queue_drain_preserves` proves that draining a queue equals the direct
sequential execution. `WBCoherent` (clean lines equal global, dirty lines are
owned) is preserved by every operation; `dirty_only_divergence` isolates the
divergence. The negative tests show that dropping a dirty line loses the write
and that a flush ignoring dirty lines leaves global stale. Assumptions:
write-back, write-allocate, one line per address, synchronous eviction; no
directory traffic, bank conflicts or hardware aliasing in this module.

## Stage 169: SLM banks and swizzling

`Intel/SlmBanks.lean` models 32 word-addressed SLM banks. `bankOf`, `banksOf`,
`maxConflict` and `transactionCount` give the conflict/cost model;
`consecutive_conflictFree` shows a warp's consecutive words are conflict-free,
`maxConflict_stride2_zero` gives the 2-way stride-2 conflict, and
`broadcast_transactionCount` covers broadcast. The XOR swizzle
`swizzleRow_conflictFree`/`swizzleColumn_conflictFree` removes both row and
column conflicts, with exact bank sets and costs; `maxConflict_naiveColumn`
and `naiveColumn_transactionCount` are the negative baseline. Assumptions: 32
banks, one request per lane group, no dual-porting, bank-width or arbitration
effects.

## Stage 170: fp16 fused multiply-add

`Intel/IeeeFp16Fma.lean` models a fused multiply-add. `productScaled_spec`
gives the exact signed product at `2^-48`; `fmaScaled` adds the third operand
before any rounding; `fmaDestExp`/`fmaDestQuantum` select the destination
binade. `fmaScaled_eq_rne` proves one round-to-nearest-even at that quantum
with ties-to-even, and `fma_fin` covers finite operands below
`4095 * 2^52`. `fma_double_rounding_counterexample` shows product-first
rounding differs from the fused result. `fmaFlags_*` covers NaN quieting,
`0 * inf` invalid, infinity, overflow and inexact. Traps, sticky lane state,
FTZ/DAZ, directed rounding and hardware FMA timing are not modeled.

## Stage 171: sticky per-lane flags

`Intel/FpFlagLanes.lean` models architectural sticky per-lane flags.
`LaneFlags` has `getLane`/`setLane`/`orLane`; `sticky_set` and `sticky_monotone`
prove flags never clear. `warpFlags` folds a lane group,
`warpFlags_projects_lane` gives the per-lane projection, and
`warpFlags_iterate`/`kernelFlags_eq_iteration_union` commute the lane and
iteration folds. Concrete overflow/inexact and invalid examples are included;
`lastWrite_loses_earlier_inexact` shows a non-sticky state loses a flag.
Trap/mask behavior, trap delivery and physical flag registers are not modeled.

## Stage 172: directed-rounding FMA

`Intel/IeeeFp16FmaDirected.lean` adds round-down, round-up and round-toward-
zero to the fused multiply-add. It proves the directed bounds and fixed
points, brackets stage 170's RNE result between down and up, gives
tie-to-even down/up bit examples and the exact overflow table per direction
(toward zero saturates at signed 65504; up-positive/down-negative go to
infinity above 65504; the other directions saturate). Product-zero reduces to
stage 159's directed add. `fmaDirected_up_ne_split` shows directed FMA is not
directed-product-then-directed-add. Traps, FTZ/DAZ, tininess-before-rounding
and hardware timing are not modeled.

## Stage 165: review stage map

`Intel/REVIEW_63.md` now carries a single stage index for stages 137--164
with their PR numbers and one-line results, and the stack range is updated to
`#64-#166`. No Lean declarations change in this stage.

## Stage 192: more register-destination ALU ops

`Intel/TlaAluExec.lean` now also executes the register-destination `mul`, `or`,
`shl`, `shr` and `asr` forms, with written-form lemmas for each.
`tlaAluStep?_mach_none` records that the multiply-high forms remain
unmodelled. The executed subset covers 54 of the 109 ALU instructions
(`tlaAlu_modeled_count`, stated on a dummy register file because `isSome` is
independent of the register contents).

## Stage 191: all ALU destinations

`Intel/TlaAlu.lean` now parses all 109 ALU instructions, including the
`acc0`/`a0`/`cr0`/`f3` destination classes. `Intel/TlaAluCensus.lean` proves
the class split: 68 `r`, 14 `acc`, 25 `addr`, 1 `cr`, 1 `flag`. Execution
(`tlaAluStep?`) still models the 68 `r`-destination forms; the other classes
are decoded but return `none` from the executor.

## Stage 190: ALU parsed/rejected census

`Intel/TlaAluCensus.lean` records the exact split between the
register-destination ALU forms and the rest of the dump. 68 instructions
parse: 4 `and`, 31 `add`, 17 `shl`, 1 `asr`, 1 `mad`, 4 `mach` and 10 `macl`.
The raw dump has 14 `mul`, 25 `shr` and 1 `or` forms with non-`r` destinations
(`acc0`, `a0`, `cr0`), plus one non-`r` `and`. Those 41 forms are the precise
next parser extension.

## Stage 189: executing the prologue ALU

`Intel/TlaAluExec.lean` executes the register-destination `and`/`add`/`mad`
subset on the logical register file. `tlaAluStep?_and/_add/_mad` give the
written form, `writeTlaMasked_self_active` gives an active destination
element, and the three prologue effects are proved:
`r127.2 = r0.0 & 0xFFFFFFC0`, `r127.2 = r127.2 + 0x280`, and
`r127.0 = r127.2 * r127.0 + 0x40`. Other ALU operations remain unmodelled
(`none`).

## Stage 188: decoding the predicated ALU forms

`Intel/TlaAlu.lean` gives the register-destination predicated ALU forms a
structured representation: operation (`and`/`add`/`mul`/`shr`/`shl`/`or`/
`asr`/`mad`/`mach`/`macl`), execution control, destination, two sources and an
optional third `mad` source. `parseTlaSrcAlu` handles the `<v;h>` shorthand.
The census proves 4 `and`, 31 `add` and 1 `mad` forms with `r` destinations,
and the prologue `and`/`add`/`mad` examples are worked out. Non-`r`
destinations (`acc0`, `a0`, `cr0`) remain outside this parser.

## Stage 187: sequencing moves and the entry effect

`Intel/TlaMovRun.lean` sequences decoded moves on the register file.
`tlaMovRun_frame` proves a run that avoids a register leaves it unchanged, and
`prologue_id_effect` composes the first two GEMM instructions: `r127` is zeroed
for 16 elements, `r2` receives `r1` for 8 elements, and every other register is
framed.

## Stage 186: executing the predicated moves

`Intel/TlaMovExec.lean` executes a decoded move on the register file.
`writeTlaMasked` writes the active destination elements (unit and stride-two
regions), `readTlaSrc` reads a GRF region or embeds a signed immediate, and
`null` is a no-op. `tlaMovStep_frame` shows only the destination register
changes. The prologue move is proved to zero `r127` for 16 elements, and the
id move to copy `r1` into `r2` for 8 elements.

## Stage 185: decoding the predicated moves

`Intel/TlaMovDecode.lean` gives the 377 `(W) mov` statements a structured
form: `(N|M0)` execution control, `rN.M<...>` destination, and a GRF or signed
immediate source. `parseTlaExec`, `parseTlaDst`, `parseTlaSrc` handle the
`r`-syntax, `null`, positive/negative immediates and the `ud`/`uw`/`f`/`hf`
width suffixes. `realTlaGemmMovs_length` proves all 377 moves parse, and the
prologue and id-move examples are worked out.

## Stage 184: the DPAS chain over BF16 values

`Intel/TlaDpasBf16.lean` gives the BF16 numeric instantiation of the DPAS
chain. `tlaBf16Step` writes both accumulator blocks with
`tlaBf16Slab`, which reads the packed source halves through `bf16Word`.
`tlaBf16Run_acc0_sum` and `_acc1_sum` prove both accumulators are the initial
block plus the ordered 32-slab sum, and `realTlaGemmDpas_bf16_sum` specializes
to the real instruction list. Source reads above the accumulator blocks are
framed by `bf16ReadA_writeTileC`/`bf16ReadB_writeTileC`.

## Stage 183: census of the predicated forms

`Intel/TlaPredCensus.lean` inventories the SYCL-TLA GEMM's 968
predicate-prefixed statements. `predOpcodes` collects their exact opcode
spellings, `predOpcodes_length` and `predOpcodes_mov_count` prove the 968 total
and 377 moves, and `predOpcodes_all_known` proves every opcode is in the
45-entry documented list (predicated moves, loads/stores, integer ALU,
`cmp`/`jmpi` predication variants, `send.gtwy`, `sync.bar`). This scopes the
next semantics stages to a finite instruction list.

## Stage 182: the second accumulator

`Intel/TlaDpasSum.lean` now also proves the `r13` half of the chain.
`tlaDpasRunSeq_acc1_sum`, `tlaDpasRun_acc1_sum` and
`realTlaGemmDpas_acc1_sum` show the second accumulator is the initial block
plus the same ordered 32-slab sum. Together with stage 181 this covers both
FP32 accumulator blocks of the real SYCL-TLA GEMM.

## Stage 181: the full 32-step DPAS sum

`Intel/TlaDpasSum.lean` proves the whole SYCL-TLA DPAS chain with a first-order
`List.sum` accumulator. `tlaDpasRunSeq_acc0_sum` and `tlaDpasRun_acc0_sum`
state that the first accumulator block is the initial block plus the ordered
sum of the 32 slabs, each read from the initial register file.
`realTlaGemmDpas_acc0_sum` specializes this to the real instruction list.
The key side conditions are the `r21/r13` accumulator bases and the `r29`
source lower bound, both proved by census. The same argument applies to
`r13`; the second-accumulator corollary is the next small step.

## Stage 180: packed BF16 register halves

`Intel/Bf16Pack.lean` adds the bit-level packing view of a DPAS source
register: `bf16Lo`/`bf16Hi` extract the two BF16 halves, `bf16Pair` packs
them, and `bf16Lo_pair`, `bf16Hi_pair` and `bf16Pair_lo_hi` prove the two views
are inverse. `tlaSlabBf16Packed` reads a slab directly from packed 32-bit
words, with a packed `1.0 * 1.0` example over depth 16.

## Stage 179: BF16 values in the DPAS slab

`Intel/Bf16Dpas.lean` embeds a decoded BF16 value into the `Word` model via
`Fixed.signed` on the `2^-7` grid and defines `tlaSlabBf16`, the BF16
instantiation of the DPAS slab. Exact examples check `1.0 * 1.0`,
`1.0 * 2.0` and an initial accumulator over depth 16. The embedding is
modulo `2^32` and is the same algebraic word model as the rest of the DPAS
development, not a floating-point rounding model.

## Stage 178: BF16 source decode

`Intel/Bf16Decode.lean` grounds the SYCL-TLA DPAS `:bf` sources in the same
`Fixed` value model as FP16. `decodeBf16` accepts finite normalized values
(exponent at least the bias) and rejects NaN, infinity, subnormals and
fractional values; `decodeBf16_some` pins the fields. Exact examples include
`1.0`, `-1.0`, `2.0` and `4.0`. `bf16ToWord` embeds the 16-bit pattern in the
high half of a 32-bit word, and `bf16Pair_low`/`_high` split a packed register
into its two BF16 halves. This is the numeric source interpretation the DPAS
chain still needs to be connected to.

## Stage 177: composing two SYCL-TLA DPAS steps

`Intel/TlaDpasFold.lean` composes the first two real DPAS instructions of the
SYCL-TLA GEMM. The first writes the accumulator blocks `r21..r28` and
`r13..r20`; the second reads A at `r34` and B at `r64`, which are disjoint from
those blocks. `readTileA_tlaDpasStep` and `readTileB_tlaDpasStep` prove the
source reads are unchanged by the accumulator write, and
`tlaDpasRun_two_acc0`/`_acc1` prove each accumulator receives
`C + slab(r30) + slab(r34)`. This is the composition pattern for the 32-step
chain; a generic fold over the full list is the next stage.

## Stage 176: register-level execution of the SYCL-TLA DPAS chain

`Intel/TlaDpasExec.lean` parses the 32 DPAS instructions of the real
SYCL-TLA GEMM into their four register bases and executes each as an 8x8
depth-16 slab on the logical register file of `Intel.FmhaExec`.
`tlaDpasStep_acc0` and `tlaDpasStep_acc1` give the two accumulator blocks
after one step, and `tlaDpasStep_frame` fixes everything else. The census
proves 32 DPAS, both accumulators always `r21`/`r13`, B bases exactly
`64..120` and A bases exactly `30..58`. The 32-step fold is defined but its
sum theorem is the next stage; the BF16 bit interpretation is also still to
come.

## Stage 175: total decoder for the SYCL-TLA dump

`Intel/TlaDecode.lean` adds `TlaInstr` and a total, lossless decoder for the
raw SYCL-TLA program. `TlaInstr` separates labels, predicate-prefixed forms
such as `(W) mov`, `dpas.8x8` with its two accumulators and two sources, and
plain instructions. `decodeTla` preserves every statement: the census proves
2252 statements, 968 predicated forms and 32 DPAS, and that every DPAS is
8x8 with execution size 16, two FP32 accumulators and two BF16 sources. This
is a decoding layer; connecting `TlaInstr` to the execution semantics is the
next stage.

## Stage 174: real SYCL-TLA GEMM import

`Intel/Examples/RealTlaGemm.lean` is the raw IGC assembly of the SYCL-TLA
GEMM example: a 256x256x32 BF16 GEMM with FP32 accumulation,
2252 statements and 32 DPAS instructions. `Intel/RealTlaGemmCoverage.lean`
proves the statement and DPAS counts, that every DPAS is `8x8` with execution
size 16, two FP32 accumulator bases and two BF16 source bases, and that the B
and A source bases range over `64..120` and `30..58` respectively. It also
proves that the current decoder rejects the program at the first `(W) mov`
prologue form, so the imported dump is a precise coverage frontier rather than
a decoded program.

## Stage 173: review stage map refresh

`Intel/REVIEW_63.md` now indexes stages 137--172 with their PR numbers and
one-line results, and the stack range is updated to `#64-#174`. The build and
audit counts are refreshed. No Lean declarations change in this stage.

## Not modeled yet

- IGC text parsing beyond the add-one and integer-GEMM forms, and general
  register aliasing (`r7:4`, `r12:2`); stages 63-66 cover those two dumps'
  operand forms and numeric aliases only.
- GEMM shapes and launches beyond the 64x64x64 integer instance; that
  instance's indices, loop, epilogue and output are stages 68-77.
- Cross-workgroup visibility, synchronization, caches and SLM aliasing; stage
  67 refines aligned accesses to bytes and proves byte-range disjointness.
- SIMD execution-mask execution, predicate logic and scoreboards. Stage 64
  interprets this kernel's broadcast and dense GRF regions, not the general
  region algebra; stage 66 models one uniform predicate bit for the GEMM's
  control flow; stages 90-93 add per-lane predicates, predicated `sel` and
  predicate `and`/`or`, register comparisons and predicated gotos; stages 92
  and 96-98 decode masks, apply them to all six real masked moves, and prove
  their frame laws, but not yet to every instruction. `gotoIf` remains a
  uniform lane-0 branch.
- SEND issue/completion/wait and the register scoreboard are stage 78; raw
  message operand layout, EOT details beyond a halted flag, and the exact SBID
  assignments (not printed in the assembly) remain.
- SLM bank layout and conflicts, sub-group masks, and barrier scheduling.
- Bitwise dword/qword register views: stage 105 supplies the storage and
  round-trip laws, stage 107 supplies the 24-lane pack/writeback layout, but
  the loop vector add's `sel`/branch sequence is not yet executed through them.
  Stage 109 proves the per-lane body output effect.
- Atomics and the launch ABI.
- IEEE-754 value semantics: stages 43-56 cover the bit layout, the value
  domain, values in units of `2 ^ -24` for normals, subnormals and fractions,
  and the glue between that scale and the numeric layer's; stage 61 covers NaN
  payload propagation and stage 80 adds `0 * inf = NaN`. A full IEEE FMA
  (subnormal arithmetic, exponent overflow/underflow, signed zero, rounding)
  remains outside the class model.
- Instruction-level DPAS: stage 79 decodes a real 8x8x32 fp8 form and shows it
  is not the model's 8x16x16 atom; the full fp8 dataflow/numerics remains.
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
61. Stage 61: NaN payloads.
62. Stage 62: a real IGC kernel imported, and its decoder coverage.
63. Stage 63: a region-aware decoder for the real kernel, failing closed on
    everything else.
64. Stage 64: execute the decoded kernel, with aliases, the address chain, and
    the per-lane load/add/store effect.
65. Stage 65: import a real 64x64x64 integer GEMM and measure the decoder's
    coverage of its control-flow shell.
66. Stage 66: decode the control-flow shell and interpret labels, predicates
    and both `goto` forms.
67. Stage 67: byte-addressed memory, alignment, aliasing and byte-range race
    freedom.
68. Stage 68: parameterise the semantics and prove the real GEMM's preamble
    and loop-entry values.
69. Stage 69: prove the loop body's A and B index computations.
70. Stage 70: prove the byte addresses, both loads, the multiply and the
    accumulation.
71. Stage 71: prove one full loop iteration and its inductive invariant.
72. Stage 72: make the GEMM loop invariant per-lane, matching the launch.
73. Stage 73: prove the GEMM epilogue's C address.
74. Stage 74: prove the K-induction over repeated loop steps.
75. Stage 75: prove the final iteration and the total `gemmDot 0 64`.
76. Stage 76: prove the epilogue store at `C`.
77. Stage 77: the real GEMM's end-to-end output theorem.
78. Stage 78: model SEND/SBID issue, completion, wait and commit.
79. Stage 79: decode a real FMHA DPAS and check the atom mapping.
80. Stage 80: refine the value step with `0 * inf = NaN`.
81. Stage 81: differential hardware conformance for the real GEMM.
82. Stage 82: import a real SIMD vector add and measure the decoder gap, with
    a fail-closed mask check.
83. Stage 83: decode scaled memory and prove the vector-add index preamble.
84. Stage 84: prove the vector-add loads and sum.
85. Stage 85: the real vector add end-to-end.
86. Stage 86: record and quantify the real DPAS atom shapes.
87. Stage 87: consolidate the issue #63 response and trusted base.
88. Stage 88: prove the 8x8x32 DPAS atom's dataflow.
89. Stage 89: negative tests for the address scale and SEND waits.
90. Stage 90: model per-lane predicates.
91. Stage 91: execute predicated select per lane.
92. Stage 92: decode M1-M8 execution masks without dropping them.
93. Stage 93: execute predicate `and` and `or` per lane.
94. Stage 94: execute register-register `cmp.lt` and `cmp.eq`.
95. Stage 95: decode predicated gotos and close vector-add coverage.
96. Stage 96: execute masked moves with M5 lane offsets.
97. Stage 97: prove stride-two masked destinations.
98. Stage 98: masked-move frames and a load-bearing mask test.
99. Stage 99: packed DPAS operands for the real FMHA atom.
100. Stage 100: prove the packed DPAS address maps are collision-free.
101. Stage 101: decode the real DPAS register bases.
102. Stage 102: execute a packed DPAS known-answer test.
103. Stage 103: parse destination regions as `<hstride>`.
104. Stage 104: import the loop vector add's tables and prove its index.
105. Stage 105: add dword storage and qword-view laws.
106. Stage 106: prove the loop body's load/add/store effect.
107. Stage 107: formalize the 24-lane pack/writeback layout.
108. Stage 108: prove the loop-carried ID selection law.
109. Stage 109: compose the real index and body into a per-lane effect.
110. Stage 110: prove the loop exits after one body.
111. Stage 111: connect global-size dwords to the continuation guard.
112. Stage 112: add per-lane control flow and branch lemmas.
113. Stage 113: materialize the decoded loop and branch sites.
114. Stage 114: prove the first guard predicate from packed halves.
115. Stage 115: prove the second guard predicate.
116. Stage 116: prove the packed low/high halves of a qword ID array.
117. Stage 117: prove the native M1/M5 pack windows.
118. Stage 118: execute dword-view moves in the loop step.
119. Stage 119: add masked dword-view move laws.
120. Stage 120: execute the real M1+M5 low pack.
121. Stage 121: execute the real M1+M5 high pack.
122. Stage 122: compose both packs into one state.
123. Stage 123: derive P3 from the executed packs.
124. Stage 124: derive P3 with preserved size dwords.
125. Stage 125: execute the increment's low pack.
126. Stage 126: execute the increment's high pack.
127. Stage 127: compose both increment packs.
128. Stage 128: prove increment packs preserve the size dwords.
129. Stage 129: derive full P6 from executed increment packs.
130. Stage 130: compose the decoded P3/P6 branches.
131. Stage 131: prove the increment add.
132. Stage 132: execute the decoded P3 prefix.
133. Stage 133: execute the decoded P6 prefix.
134. Stage 134: execute the decoded body slice.
135. Stage 135: execute the decoded entry slice.
136. Stage 136: compose the per-lane decoded control path.
137. Stage 137: prove the per-lane memory effect on the decoded path.
138. Stage 138: derive the path guards from the decoded prefix.
139. Stage 139: per-location visibility and release/acquire.
140. Stage 140: the decoded kernel entry from PC 0.
141. Stage 141: generic execution-mask laws.
142. Stage 142: FMHA atom value refinement and tile composition.
143. Stage 143: predicated lanes write nothing.
144. Stage 144: reaching `ret` with the halt flag.
145. Stage 145: global/SLM disjointness and workgroup barriers.
146. Stage 146: grid-stride indices and store composition.
147. Stage 147: SBID fields in an encoded SEND descriptor.
148. Stage 148: fp8 E4M3 decode for the FMHA atom.
149. Stage 149: IEEE fp16 addition rounding.
150. Stage 150: register-level FMHA DPAS execution.
151. Stage 151: mask-aware execution for the loop body.
152. Stage 152: cross-lane race freedom.
153. Stage 153: composing the 32 lane stores.
154. Stage 154: write-through cache coherence.
155. Stage 155: register-level FMHA mainloop.
156. Stage 156: fp16 special values and overflow.
157. Stage 157: coherence traffic between two caches.
158. Stage 158: the decoded loop-back block.
159. Stage 159: directed fp16 rounding.
160. Stage 160: dword/qword coalescing adapter.
161. Stage 161: n-iteration grid-stride induction.
162. Stage 162: directory/ownership coherence.
163. Stage 163: FMHA tail and partial K.
164. Stage 164: general fp16 round-to-nearest-even.
165. Stage 165: refresh the review stage map.
166. Stage 166: fp exception flags.
167. Stage 167: relaxed atomics and store buffers.
168. Stage 168: write-back caches and request queues.
169. Stage 169: SLM banks and swizzling.
170. Stage 170: fp16 fused multiply-add.
171. Stage 171: sticky per-lane flags.
172. Stage 172: directed-rounding FMA.
173. Stage 173: review stage map refresh.
174. Stage 174: real SYCL-TLA GEMM import.
175. Stage 175: total decoder for the SYCL-TLA dump.
176. Stage 176: register-level execution of the SYCL-TLA DPAS chain.
177. Stage 177: composing two SYCL-TLA DPAS steps.
178. Stage 178: BF16 source decode.
179. Stage 179: BF16 values in the DPAS slab.
180. Stage 180: packed BF16 register halves.
181. Stage 181: the full 32-step DPAS sum.
182. Stage 182: the second accumulator.
183. Stage 183: census of the predicated forms.
184. Stage 184: the DPAS chain over BF16 values.
185. Stage 185: decoding the predicated moves.
186. Stage 186: executing the predicated moves.
187. Stage 187: sequencing moves and the entry effect.
188. Stage 188: decoding the predicated ALU forms.
189. Stage 189: executing the prologue ALU.
190. Stage 190: ALU parsed/rejected census.
191. Stage 191: all ALU destinations.
192. Stage 192 (this PR): more register-destination ALU ops.
