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

## Not modeled yet

- IGC text parsing and register aliases (`r7:4`, `r12:2`).
- The compiler-generated prolog and global-id / address computation.
- SIMD masks, GRF regions, predicates, and scoreboards.
- SEND/EOT details beyond a halted flag.
- SLM bank layout and conflicts, sub-group masks, and barrier scheduling.
- Atomics and the launch ABI.
- Bit-level fp16/bf16 rounding: stages 29-31 derive the per-step error from
  concrete quantum roundings including ties-to-even, but IEEE-754 subnormals
  and the fp16 exponent range are not modeled.
- Instruction-level DPAS dispatch (the atom is modeled as a tile operation).
- Strided per-thread staging as SYCL-TLA's copy atoms use it: stage 37 models
  a block distribution (lane `l` owns a contiguous chunk), not the interleaved
  per-thread addressing.

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
37. Stage 37 (this PR): distributed staging across lanes.
