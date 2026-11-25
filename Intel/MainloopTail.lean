-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.Mainloop

@[expose] public section

/-!
# Executed tail slab

The mainloop of stage 25 needs `K = T * d`. Real depths are not multiples of
the atom depth, so the last slab is partial: only `r < d` columns of A and `r`
rows of B contribute.

`tailProg t r` stages that partial slab from slab index `t` and issues a
depth-`r` DPAS. `mainloop_tail_correct` runs the full mainloop and then the
tail, halting with the C tile equal to `dotMat` at depth `T * d + r`.

SLM layout for the tail: `slm (m * r + k)` holds `A[i + m][t * d + k]` and
`slm (M * r + k * N + n)` holds `B[t * d + k][j + n]`.
-/

namespace IntelGpu

def tailProg (t r : Nat) : List KInstr :=
  [.stageATail t r, .stageBTail t r, .barrier, .dpasTail r]

/-- SLM contents after staging the tail slab. -/
def stagedTail (g : Geom) (s : KState) (t0 r : Nat) : Nat → Word :=
  copyStrided (copyStrided s.slm s.mem 0 (g.aBase + g.i * g.ldA + t0 * g.d) g.ldA r g.M)
    s.mem (g.M * r) (g.bBase + t0 * g.d * g.ldB + g.j) g.ldB g.N r

theorem stagedTail_A (g : Geom) (A : Nat → Nat → Word) (mem : Nat → Word)
    (hA : ∀ row col, mem (g.aBase + row * g.ldA + col) = A row col)
    (s : KState) (h : s.mem = mem) (t0 r : Nat) :
    ∀ m < g.M, ∀ k < r, stagedTail g s t0 r (m * r + k) = A (g.i + m) (t0 * g.d + k) := by
  intro m hm k hk
  have hframe : ∀ q < r, ∀ j < g.N, m * r + k ≠ g.M * r + q * g.N + j := by
    intro q _ j _
    have h1 : m * r + r ≤ g.M * r := by
      have := Nat.mul_le_mul_right r (by omega : m + 1 ≤ g.M)
      rwa [Nat.succ_mul] at this
    omega
  have hB' := copyStrided_frame
    (copyStrided s.slm mem 0 (g.aBase + g.i * g.ldA + t0 * g.d) g.ldA r g.M) mem
    (g.M * r) (g.bBase + t0 * g.d * g.ldB + g.j) g.ldB g.N
    r (m * r + k) hframe
  have hval := copyStrided_value s.slm mem 0 (g.aBase + g.i * g.ldA + t0 * g.d) g.ldA r
    g.M m k hm hk
  rw [Nat.zero_add] at hval
  rw [stagedTail, h, hB', hval]
  have hrow : g.aBase + g.i * g.ldA + t0 * g.d + m * g.ldA + k =
      g.aBase + (g.i + m) * g.ldA + t0 * g.d + k := by
    rw [Nat.add_mul]
    omega
  rw [hrow]
  simpa [Nat.add_assoc] using hA (g.i + m) (t0 * g.d + k)

theorem stagedTail_B (g : Geom) (B : Nat → Nat → Word) (mem : Nat → Word)
    (hB : ∀ row col, mem (g.bBase + row * g.ldB + col) = B row col)
    (s : KState) (h : s.mem = mem) (t0 r : Nat) :
    ∀ k < r, ∀ n < g.N,
      stagedTail g s t0 r (g.M * r + k * g.N + n) = B (t0 * g.d + k) (g.j + n) := by
  intro k hk n hn
  have hval := copyStrided_value
    (copyStrided s.slm mem 0 (g.aBase + g.i * g.ldA + t0 * g.d) g.ldA r g.M) mem
    (g.M * r) (g.bBase + t0 * g.d * g.ldB + g.j) g.ldB g.N r k n hk hn
  rw [stagedTail, h, hval]
  have hrow : g.bBase + t0 * g.d * g.ldB + g.j + k * g.ldB + n =
      g.bBase + (t0 * g.d + k) * g.ldB + (g.j + n) := by
    rw [Nat.add_mul]
    omega
  rw [hrow]
  simpa [Nat.add_assoc] using hB (t0 * g.d + k) (g.j + n)

theorem krun_mem (g : Geom) (prog : List KInstr) :
    ∀ (n : Nat) (s : KState), (krun g prog n s).mem = s.mem := by
  intro n
  induction n with
  | zero => intro s; rfl
  | succ n ih =>
      intro s
      rw [krun_succ, ih]
      cases h : prog[s.pc]? with
      | none => simp [kstep, h]
      | some i => cases i <;> simp [kstep, h]

/-- The tail: stage, sync, and accumulate a depth-`r` slab on top of a
depth-`t0 * d` accumulator. -/
theorem tail_correct (g : Geom) (A B : Nat → Nat → Word) (mem : Nat → Word)
    (hA : ∀ row col, mem (g.aBase + row * g.ldA + col) = A row col)
    (hB : ∀ row col, mem (g.bBase + row * g.ldB + col) = B row col)
    (t0 r : Nat) (s : KState)
    (hacc0 : ∀ m < g.M, ∀ n < g.N,
      s.acc m n = dotMatFrom A B (g.i + m) (g.j + n) 0 (t0 * g.d))
    (hmem : s.mem = mem) (hpc : s.pc = 0) :
    ∀ m < g.M, ∀ n < g.N,
      (krun g (tailProg t0 r) 4 s).acc m n =
        dotMatFrom A B (g.i + m) (g.j + n) 0 (t0 * g.d + r) := by
  intro m hm n hn
  have hacc : (krun g (tailProg t0 r) 4 s).acc m n =
      s.acc m n + dpasSlab r (fun k m' => stagedTail g s t0 r (m' * r + k))
        (fun k n' => stagedTail g s t0 r (g.M * r + k * g.N + n')) m n := by
    simp [tailProg, krun, kstep, stagedTail, hpc]
  rw [hacc, hacc0 m hm n hn]
  rw [dpasSlab_congr r (fun k m' => stagedTail g s t0 r (m' * r + k))
    (fun k m' => A (g.i + m') (t0 * g.d + k))
    (fun k n' => stagedTail g s t0 r (g.M * r + k * g.N + n'))
    (fun k n' => B (t0 * g.d + k) (g.j + n')) m n
    (fun k hk => stagedTail_A g A mem hA s hmem t0 r m hm k hk)
    (fun k hk => stagedTail_B g B mem hB s hmem t0 r k hk n hn)]
  rw [dpasSlab_eq_dotMatFrom A B g.i g.j (t0 * g.d) r m n]
  rw [dotMatFrom_append]
  rw [show 0 + t0 * g.d = t0 * g.d by omega]

/-- The full executed pipeline for arbitrary depth: `T` full slabs plus a
depth-`r` tail give `dotMat` at depth `T * d + r`. -/
theorem mainloop_tail_correct (g : Geom) (A B : Nat → Nat → Word) (mem : Nat → Word)
    (hA : ∀ row col, mem (g.aBase + row * g.ldA + col) = A row col)
    (hB : ∀ row col, mem (g.bBase + row * g.ldB + col) = B row col)
    (T r : Nat) :
    let s1 := krun g (mainloopProg T) (8 * T + 3) (kHead mem (fun _ _ => 0))
    let s2 := krun g (tailProg T r) 4 { s1 with pc := 0 }
    s1.halted = true ∧
      ∀ m < g.M, ∀ n < g.N,
        s2.acc m n = dotMat A B (g.i + m) (g.j + n) (T * g.d + r) := by
  have hloop := mainloop_correct g A B mem hA hB T
  have hmem : (krun g (mainloopProg T) (8 * T + 3) (kHead mem (fun _ _ => 0))).mem = mem :=
    krun_mem g (mainloopProg T) (8 * T + 3) _
  dsimp only at hloop ⊢
  refine ⟨hloop.1, ?_⟩
  intro m hm n hn
  exact tail_correct g A B mem hA hB T r
    { krun g (mainloopProg T) (8 * T + 3) (kHead mem (fun _ _ => 0)) with pc := 0 }
    (by intro m' hm' n' hn'; exact hloop.2.2 m' hm' n' hn') hmem rfl m hm n hn

end IntelGpu
