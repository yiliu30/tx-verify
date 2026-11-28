-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.Staging

@[expose] public section

/-!
# The kernel mainloop: stage, sync, DPAS

Stages 18 and 24 verified the DPAS slab and the SLM staging separately. This
module runs them as one loop, the shape of the SYCL-TLA mainloop:

```
for t in 0 .. T:
  stage A slab t   (strided copy from global into SLM)
  stage B slab t   (strided copy from global into SLM)
  barrier
  dpas             (accumulate the slab into the C tile)
```

SLM layout: `slm (m * d + k)` holds `A[i + m][t * d + k]` and
`slm (M * d + k * N + n)` holds `B[t * d + k][j + n]`.

Proved: `mainloop_correct` — `8 * T + 3` steps halt with the accumulator tile
equal to `dotMat` at depth `T * d`, and `T` barriers retired.
-/

namespace IntelGpu

/-- Copy `rows` runs of `count` words: source rows are `ld` apart, destination
rows are packed. -/
def copyStrided (dstMem srcMem : Nat → Word) (dst rowSrc ld count : Nat) :
    Nat → Nat → Word
  | 0 => dstMem
  | rows + 1 =>
      copyN (copyStrided dstMem srcMem dst rowSrc ld count rows) srcMem
        (dst + rows * count) (rowSrc + rows * ld) count

theorem copyStrided_value (dstMem srcMem : Nat → Word) (dst rowSrc ld count : Nat) :
    ∀ (rows r k : Nat), r < rows → k < count →
      copyStrided dstMem srcMem dst rowSrc ld count rows (dst + r * count + k) =
        srcMem (rowSrc + r * ld + k) := by
  intro rows
  induction rows with
  | zero => intro r k hr _; omega
  | succ rows ih =>
      intro r k hr hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hlt | heq
      · rw [copyStrided]
        have hframe : ∀ j < count, dst + r * count + k ≠ dst + rows * count + j := by
          intro j hj
          have hbound : r * count + count ≤ rows * count := by
            have hle := Nat.mul_le_mul_right count (by omega : r + 1 ≤ rows)
            rwa [Nat.succ_mul] at hle
          omega
        rw [copyN_frame _ _ _ _ _ _ hframe]
        exact ih r k hlt hk
      · rw [heq, copyStrided]
        have hv := copyN_value (copyStrided dstMem srcMem dst rowSrc ld count rows) srcMem
          (dst + rows * count) (rowSrc + rows * ld) count k hk
        simpa [Nat.add_assoc] using hv

theorem copyStrided_frame (dstMem srcMem : Nat → Word) (dst rowSrc ld count : Nat) :
    ∀ (rows a : Nat), (∀ r < rows, ∀ k < count, a ≠ dst + r * count + k) →
      copyStrided dstMem srcMem dst rowSrc ld count rows a = dstMem a := by
  intro rows
  induction rows with
  | zero => intro a _; rfl
  | succ rows ih =>
      intro a h
      rw [copyStrided]
      rw [copyN_frame _ _ _ _ _ _ (by
        intro j hj
        exact h rows (Nat.lt_succ_self rows) j hj)]
      exact ih a (by intro r hr k hk; exact h r (by omega) k hk)

/-- `dpasSlab` reads the A tile only at the tile's own output row and the B tile
only at its own output column, so pointwise agreement on depth slots suffices. -/
theorem dpasSlab_congr (d : Nat) :
    ∀ (A A' B B' : Nat → Nat → Word) (m n : Nat),
      (∀ k < d, A k m = A' k m) → (∀ k < d, B k n = B' k n) →
      dpasSlab d A B m n = dpasSlab d A' B' m n := by
  induction d with
  | zero => intro A A' B B' m n _ _; rfl
  | succ d ih =>
      intro A A' B B' m n hA hB
      rw [dpasSlab, dpasSlab, hA 0 (Nat.zero_lt_succ d), hB 0 (Nat.zero_lt_succ d)]
      congr 1
      apply ih
      · intro k hk
        simpa [Nat.add_assoc] using hA (k + 1) (by omega)
      · intro k hk
        simpa [Nat.add_assoc] using hB (k + 1) (by omega)

/-- GEMM geometry for one workgroup tile. -/
structure Geom where
  aBase : Nat
  ldA : Nat
  bBase : Nat
  ldB : Nat
  i : Nat
  j : Nat
  d : Nat
  M : Nat
  N : Nat

structure KState where
  mem : Nat → Word
  slm : Nat → Word
  acc : Nat → Nat → Word
  t : Nat
  phase : Nat
  pred : Bool
  pc : Nat
  halted : Bool

inductive KInstr where
  | stageA
  | stageB
  | barrier
  | dpas
  | incT
  | cmpGe (T : Nat)
  | jmpiIf (target : Nat)
  | jmpi (target : Nat)
  /-- Stage the `r`-deep tail columns of slab `t` of A. -/
  | stageATail (t r : Nat)
  /-- Stage the `r`-deep tail rows of slab `t` of B. -/
  | stageBTail (t r : Nat)
  /-- Accumulate the `r`-deep tail slab. -/
  | dpasTail (r : Nat)
  deriving Repr

/-- SLM contents after staging slab `t0`. -/
def staged (g : Geom) (s : KState) (t0 : Nat) : Nat → Word :=
  copyStrided (copyStrided s.slm s.mem 0 (g.aBase + g.i * g.ldA + t0 * g.d) g.ldA g.d g.M)
    s.mem (g.M * g.d) (g.bBase + t0 * g.d * g.ldB + g.j) g.ldB g.N g.d

def kstep (g : Geom) (prog : List KInstr) (s : KState) : KState :=
  match prog[s.pc]? with
  | none => { s with halted := true }
  | some .stageA =>
      { s with
        slm := copyStrided s.slm s.mem 0 (g.aBase + g.i * g.ldA + s.t * g.d) g.ldA g.d g.M,
        pc := s.pc + 1 }
  | some .stageB =>
      { s with
        slm := copyStrided s.slm s.mem (g.M * g.d)
          (g.bBase + s.t * g.d * g.ldB + g.j) g.ldB g.N g.d,
        pc := s.pc + 1 }
  | some .barrier => { s with phase := s.phase + 1, pc := s.pc + 1 }
  | some .dpas =>
      { s with
        acc := fun m n =>
          s.acc m n + dpasSlab g.d (fun k m' => s.slm (m' * g.d + k))
            (fun k n' => s.slm (g.M * g.d + k * g.N + n')) m n,
        pc := s.pc + 1 }
  | some .incT => { s with t := s.t + 1, pc := s.pc + 1 }
  | some (.cmpGe T) => { s with pred := decide (T ≤ s.t), pc := s.pc + 1 }
  | some (.jmpiIf target) => { s with pc := if s.pred then target else s.pc + 1 }
  | some (.jmpi target) => { s with pc := target }
  | some (.stageATail t r) =>
      { s with
        slm := copyStrided s.slm s.mem 0 (g.aBase + g.i * g.ldA + t * g.d) g.ldA r g.M,
        pc := s.pc + 1 }
  | some (.stageBTail t r) =>
      { s with
        slm := copyStrided s.slm s.mem (g.M * r)
          (g.bBase + t * g.d * g.ldB + g.j) g.ldB g.N r,
        pc := s.pc + 1 }
  | some (.dpasTail r) =>
      { s with
        acc := fun m n =>
          s.acc m n + dpasSlab r (fun k m' => s.slm (m' * r + k))
            (fun k n' => s.slm (g.M * r + k * g.N + n')) m n,
        pc := s.pc + 1 }

def krun (g : Geom) (prog : List KInstr) : Nat → KState → KState
  | 0, s => s
  | n + 1, s => krun g prog n (kstep g prog s)

@[simp] theorem krun_zero (g : Geom) (prog : List KInstr) (s : KState) :
    krun g prog 0 s = s := rfl

@[simp] theorem krun_succ (g : Geom) (prog : List KInstr) (n : Nat) (s : KState) :
    krun g prog (n + 1) s = krun g prog n (kstep g prog s) := rfl

theorem krun_add (g : Geom) (prog : List KInstr) (a b : Nat) (s : KState) :
    krun g prog (a + b) s = krun g prog b (krun g prog a s) := by
  induction a generalizing s with
  | zero => simp
  | succ a ih =>
      calc
        krun g prog (a + 1 + b) s = krun g prog (a + b) (kstep g prog s) := by
          rw [show a + 1 + b = (a + b) + 1 by omega]
          rfl
        _ = krun g prog b (krun g prog a (kstep g prog s)) := ih (kstep g prog s)
        _ = krun g prog b (krun g prog (a + 1) s) := rfl

def mainloopProg (T : Nat) : List KInstr :=
  [.cmpGe T, .jmpiIf 8, .stageA, .stageB, .barrier, .dpas, .incT, .jmpi 0]

def kHead (mem : Nat → Word) (acc : Nat → Nat → Word) : KState :=
  { mem := mem, slm := fun _ => 0, acc := acc, t := 0, phase := 0, pred := false,
    pc := 0, halted := false }

structure KInv (g : Geom) (A B : Nat → Nat → Word) (mem : Nat → Word) (t0 : Nat)
    (s : KState) : Prop where
  accEq : ∀ m < g.M, ∀ n < g.N,
    s.acc m n = dotMatFrom A B (g.i + m) (g.j + n) 0 (t0 * g.d)
  phaseEq : s.phase = t0
  tEq : s.t = t0
  predF : s.pred = false
  pc0 : s.pc = 0
  haltF : s.halted = false
  memEq : s.mem = mem

theorem staged_A (g : Geom) (A : Nat → Nat → Word) (mem : Nat → Word)
    (hA : ∀ row col, mem (g.aBase + row * g.ldA + col) = A row col)
    (s : KState) (h : s.mem = mem) (t0 : Nat) :
    ∀ m < g.M, ∀ k < g.d, staged g s t0 (m * g.d + k) = A (g.i + m) (t0 * g.d + k) := by
  intro m hm k hk
  have hframe : ∀ r < g.d, ∀ j < g.N, m * g.d + k ≠ g.M * g.d + r * g.N + j := by
    intro r _ j _
    have h1 : m * g.d + g.d ≤ g.M * g.d := by
      have := Nat.mul_le_mul_right g.d (by omega : m + 1 ≤ g.M)
      rwa [Nat.succ_mul] at this
    omega
  have hB' := copyStrided_frame
    (copyStrided s.slm mem 0 (g.aBase + g.i * g.ldA + t0 * g.d) g.ldA g.d g.M) mem
    (g.M * g.d) (g.bBase + t0 * g.d * g.ldB + g.j) g.ldB g.N
    g.d (m * g.d + k) hframe
  have hval := copyStrided_value s.slm mem 0 (g.aBase + g.i * g.ldA + t0 * g.d) g.ldA g.d
    g.M m k hm hk
  rw [Nat.zero_add] at hval
  rw [staged, h, hB', hval]
  have hrow : g.aBase + g.i * g.ldA + t0 * g.d + m * g.ldA + k =
      g.aBase + (g.i + m) * g.ldA + t0 * g.d + k := by
    rw [Nat.add_mul]
    omega
  rw [hrow]
  simpa [Nat.add_assoc] using hA (g.i + m) (t0 * g.d + k)

theorem staged_B (g : Geom) (B : Nat → Nat → Word) (mem : Nat → Word)
    (hB : ∀ row col, mem (g.bBase + row * g.ldB + col) = B row col)
    (s : KState) (h : s.mem = mem) (t0 : Nat) :
    ∀ k < g.d, ∀ n < g.N,
      staged g s t0 (g.M * g.d + k * g.N + n) = B (t0 * g.d + k) (g.j + n) := by
  intro k hk n hn
  have hval := copyStrided_value
    (copyStrided s.slm mem 0 (g.aBase + g.i * g.ldA + t0 * g.d) g.ldA g.d g.M) mem
    (g.M * g.d) (g.bBase + t0 * g.d * g.ldB + g.j) g.ldB g.N g.d k n hk hn
  rw [staged, h, hval]
  have hrow : g.bBase + t0 * g.d * g.ldB + g.j + k * g.ldB + n =
      g.bBase + (t0 * g.d + k) * g.ldB + (g.j + n) := by
    rw [Nat.add_mul]
    omega
  rw [hrow]
  simpa [Nat.add_assoc] using hB (t0 * g.d + k) (g.j + n)

theorem kstep_iter (g : Geom) (A B : Nat → Nat → Word) (mem : Nat → Word)
    (hA : ∀ row col, mem (g.aBase + row * g.ldA + col) = A row col)
    (hB : ∀ row col, mem (g.bBase + row * g.ldB + col) = B row col)
    (T t0 : Nat) (s : KState) (h : KInv g A B mem t0 s) (ht : t0 < T) :
    KInv g A B mem (t0 + 1) (krun g (mainloopProg T) 8 s) := by
  have hknot : ¬ T ≤ t0 := by omega
  have hacc : ∀ m n, (krun g (mainloopProg T) 8 s).acc m n =
      s.acc m n + dpasSlab g.d (fun k m' => staged g s t0 (m' * g.d + k))
        (fun k n' => staged g s t0 (g.M * g.d + k * g.N + n')) m n := by
    intro m n
    simp [mainloopProg, krun, kstep, staged, h.pc0, h.tEq, hknot]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m hm n hn
    rw [hacc m n, h.accEq m hm n hn]
    rw [dpasSlab_congr g.d (fun k m' => staged g s t0 (m' * g.d + k))
      (fun k m' => A (g.i + m') (t0 * g.d + k))
      (fun k n' => staged g s t0 (g.M * g.d + k * g.N + n'))
      (fun k n' => B (t0 * g.d + k) (g.j + n')) m n
      (fun k hk => staged_A g A mem hA s h.memEq t0 m hm k hk)
      (fun k hk => staged_B g B mem hB s h.memEq t0 k hk n hn)]
    rw [dpasSlab_eq_dotMatFrom A B g.i g.j (t0 * g.d) g.d m n, Nat.succ_mul]
    rw [dotMatFrom_append]
    rw [show 0 + t0 * g.d = t0 * g.d by omega]
  · simp [mainloopProg, krun, kstep, h.pc0, h.tEq, hknot, h.phaseEq]
  · simp [mainloopProg, krun, kstep, h.pc0, h.tEq, hknot]
  · simp [mainloopProg, krun, kstep, h.pc0, h.tEq, hknot]
  · simp [mainloopProg, krun, kstep, h.pc0, h.tEq, hknot]
  · simp [mainloopProg, krun, kstep, h.pc0, h.tEq, hknot, h.haltF]
  · simp [mainloopProg, krun, kstep, h.pc0, h.tEq, hknot, h.memEq]

theorem kstep_exit (g : Geom) (A B : Nat → Nat → Word) (mem : Nat → Word)
    (T : Nat) (s : KState) (h : KInv g A B mem T s) :
    (krun g (mainloopProg T) 3 s).halted = true := by
  have hle : T ≤ s.t := by rw [h.tEq]; omega
  simp [mainloopProg, krun, kstep, h.pc0, hle]

theorem mainloop_run_aux (g : Geom) (A B : Nat → Nat → Word) (mem : Nat → Word)
    (hA : ∀ row col, mem (g.aBase + row * g.ldA + col) = A row col)
    (hB : ∀ row col, mem (g.bBase + row * g.ldB + col) = B row col) (T : Nat) :
    ∀ (n : Nat) (t0 : Nat) (s : KState), t0 + n = T → KInv g A B mem t0 s →
      (krun g (mainloopProg T) (8 * n + 3) s).halted = true ∧
        (krun g (mainloopProg T) (8 * n + 3) s).phase = T ∧
        ∀ m < g.M, ∀ n' < g.N,
          (krun g (mainloopProg T) (8 * n + 3) s).acc m n' =
            dotMatFrom A B (g.i + m) (g.j + n') 0 (T * g.d) := by
  intro n
  induction n with
  | zero =>
      intro t0 s ht h
      have ht0 : t0 = T := by omega
      have hT : KInv g A B mem T s := ht0 ▸ h
      have hle : T ≤ s.t := by rw [hT.tEq]; omega
      refine ⟨?_, ?_, ?_⟩
      · simpa using kstep_exit g A B mem T s hT
      · have hphase : (krun g (mainloopProg T) (8 * 0 + 3) s).phase = s.phase := by
          simp [mainloopProg, krun, kstep, hT.pc0, hle]
        rw [hphase, hT.phaseEq]
      · intro m hm n' hn'
        have hacc : (krun g (mainloopProg T) (8 * 0 + 3) s).acc m n' = s.acc m n' := by
          simp [mainloopProg, krun, kstep, hT.pc0, hle]
        rw [hacc, hT.accEq m hm n' hn']
  | succ n ih =>
      intro t0 s ht h
      have hlt : t0 < T := by omega
      have hnext : t0 + 1 + n = T := by omega
      have hiter := kstep_iter g A B mem hA hB T t0 s h hlt
      have hrun : krun g (mainloopProg T) (8 * (n + 1) + 3) s =
          krun g (mainloopProg T) (8 * n + 3) (krun g (mainloopProg T) 8 s) := by
        rw [show 8 * (n + 1) + 3 = 8 + (8 * n + 3) by omega]
        exact krun_add g (mainloopProg T) 8 (8 * n + 3) s
      rw [hrun]
      exact ih (t0 + 1) (krun g (mainloopProg T) 8 s) hnext hiter

/-- The composed mainloop: `8 * T + 3` steps stage, sync, and accumulate all
`T` slabs, halting with the C tile equal to `dotMat` at depth `T * d`. -/
theorem mainloop_correct (g : Geom) (A B : Nat → Nat → Word) (mem : Nat → Word)
    (hA : ∀ row col, mem (g.aBase + row * g.ldA + col) = A row col)
    (hB : ∀ row col, mem (g.bBase + row * g.ldB + col) = B row col) (T : Nat) :
    let s' := krun g (mainloopProg T) (8 * T + 3) (kHead mem (fun _ _ => 0))
    s'.halted = true ∧ s'.phase = T ∧
      ∀ m < g.M, ∀ n < g.N,
        s'.acc m n = dotMat A B (g.i + m) (g.j + n) (T * g.d) := by
  have hinit : KInv g A B mem 0 (kHead mem (fun _ _ => 0)) :=
    ⟨by intro m _ n _; simp [kHead, dotMatFrom], rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hres := mainloop_run_aux g A B mem hA hB T T 0 (kHead mem (fun _ _ => 0))
    (by omega) hinit
  dsimp only
  refine ⟨hres.1, hres.2.1, ?_⟩
  intro m hm n hn
  rw [hres.2.2 m hm n hn]
  rfl

end IntelGpu
