-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.GemmAssembly

@[expose] public section

/-!
# Operand staging: global memory into SLM

The DPAS layer (stage 18) and the instance (stage 19) assume the A and B
operand slabs are already in tile registers. This module produces them: a bulk
copy stages an `M x d` A slab and an `N x d` B slab from global memory into
SLM, a barrier retires, and the DPAS operands are read out of SLM.

SLM layout (row-major within the slab):

- `slm (m * d + k)` holds `A[i + m][t + k]`
- `slm (M * d + n * d + k)` holds `B[t + k][j + n]`

so the operand tiles are exactly `fun k m => slm (m * d + k)` and
`fun k n => slm (M * d + n * d + k)`.
-/

namespace IntelGpu

/-- Copy `n` words from `srcMem` at `src` into `dstMem` at `dst`, last write
wins. -/
def copyN (dstMem srcMem : Nat → Word) (dst src : Nat) : Nat → Nat → Word
  | 0 => dstMem
  | n + 1 => update (copyN dstMem srcMem dst src n) (dst + n) (srcMem (src + n))

theorem copyN_value (dstMem srcMem : Nat → Word) (dst src n k : Nat) (hk : k < n) :
    copyN dstMem srcMem dst src n (dst + k) = srcMem (src + k) := by
  induction n with
  | zero => omega
  | succ n ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | heq
      · have hne : dst + k ≠ dst + n := by omega
        rw [copyN, update_away _ _ _ _ hne]
        exact ih hlt
      · subst heq
        rw [copyN, update_at]

theorem copyN_frame (dstMem srcMem : Nat → Word) (dst src n : Nat) (a : Nat)
    (h : ∀ k < n, a ≠ dst + k) : copyN dstMem srcMem dst src n a = dstMem a := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [copyN, update_away _ _ _ _ (h n (Nat.lt_succ_self n))]
      exact ih (by intro k hk; exact h k (by omega))

structure SState where
  mem : Nat → Word
  slm : Nat → Word
  phase : Nat
  halted : Bool

inductive SInstr where
  | copy (dst src count : Nat)
  | barrier
  | eot
  deriving Repr

def sstep (s : SState) : SInstr → SState
  | .copy dst src count => { s with slm := copyN s.slm s.mem dst src count }
  | .barrier => { s with phase := s.phase + 1 }
  | .eot => { s with halted := true }

def srun (s : SState) (is : List SInstr) : SState := is.foldl sstep s

@[simp] theorem srun_nil (s : SState) : srun s [] = s := rfl

@[simp] theorem srun_cons (s : SState) (i : SInstr) (is : List SInstr) :
    srun s (i :: is) = srun (sstep s i) is := rfl

/-- Initial staging state: SLM starts zeroed. -/
def sHead (mem : Nat → Word) : SState :=
  { mem := mem, slm := fun _ => 0, phase := 0, halted := false }

/-- The staging program for one K slab: copy the A slab, copy the B slab, sync. -/
def stageSlabProg (aBase bBase d M N : Nat) : List SInstr :=
  [.copy 0 aBase (M * d), .copy (M * d) bBase (N * d), .barrier]

theorem stageSlab_correct (mem : Nat → Word) (aBase bBase d M N : Nat) :
    let s := srun (sHead mem) (stageSlabProg aBase bBase d M N)
    s.phase = 1 ∧ s.halted = false ∧
      (∀ k < d, ∀ m < M, s.slm (m * d + k) = mem (aBase + m * d + k)) ∧
      (∀ k < d, ∀ n < N, s.slm (M * d + n * d + k) = mem (bBase + n * d + k)) := by
  have hA : ∀ a, a < M * d →
      copyN (copyN (fun _ => (0 : Word)) mem 0 aBase (M * d)) mem (M * d) bBase (N * d) a =
        copyN (fun _ => (0 : Word)) mem 0 aBase (M * d) a := by
    intro a ha
    apply copyN_frame
    intro k hk
    omega
  have hkA : ∀ (m Bnd : Nat), m < Bnd → m * d + d ≤ Bnd * d := by
    intro m Bnd hm
    have h1 : (m + 1) * d ≤ Bnd * d := Nat.mul_le_mul_right d (by omega)
    rwa [Nat.succ_mul] at h1
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro k hk m hm
    have hbound : m * d + k < M * d := by
      have := hkA m M hm
      omega
    simp only [srun, stageSlabProg, sstep, sHead, List.foldl]
    rw [hA (m * d + k) hbound]
    have hv := copyN_value (fun _ => (0 : Word)) mem 0 aBase (M * d) (m * d + k) hbound
    rw [Nat.zero_add] at hv
    simpa [Nat.add_assoc] using hv
  · intro k hk n hn
    have hbound : n * d + k < N * d := by
      have := hkA n N hn
      omega
    simp only [srun, stageSlabProg, sstep, sHead, List.foldl]
    have hv := copyN_value (copyN (fun _ => (0 : Word)) mem 0 aBase (M * d)) mem
      (M * d) bBase (N * d) (n * d + k) hbound
    simpa [Nat.add_assoc] using hv

/-- With `mem (aBase + m*d + k) = A (i+m) (t+k)`, the staged A tile is exactly
the DPAS A operand slab. -/
theorem dpas_from_staged (A : Nat → Nat → Word) (mem : Nat → Word)
    (aBase bBase i t d M N : Nat)
    (hA : ∀ k < d, ∀ m < M, mem (aBase + m * d + k) = A (i + m) (t + k)) :
    let s := srun (sHead mem) (stageSlabProg aBase bBase d M N)
    ∀ k < d, ∀ m < M, (fun k m => s.slm (m * d + k)) k m = A (i + m) (t + k) := by
  have hblk := stageSlab_correct mem aBase bBase d M N
  dsimp only at hblk ⊢
  intro k hk m hm
  rw [hblk.2.2.1 k hk m hm]
  exact hA k hk m hm

end IntelGpu
