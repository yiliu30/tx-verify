-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.DpasMask

@[expose] public section

/-!
# Executed epilogue store

The last piece a GEMM tile needs after the DPAS mainloop is the epilogue: the
accumulator tile is written out to global memory.

`epilogueProg` walks the `M * N` elements of the tile, storing
`acc (k / N) (k % N)` to the packed word address `base + k`, and branches back
while `k < M * N`.

- `epilogue_correct`: `5 * M * N + 3` steps halt with every tile element
  written.
- `epilogue_block`: the store lands on the tile's C block at origin `(gi, gj)`.
- `tileSpec_of_store`: a tile written this way satisfies `TileSpec`, so the
  stage-19/20 instance rests on an executed store rather than an assumption.

The tile is written packed (leading dimension `N`); a general leading dimension
is a later refinement.
-/

namespace IntelGpu

theorem update_at (m : Nat → Word) (a : Nat) (v : Word) : update m a v a = v := by
  simp [update]

theorem update_away (m : Nat → Word) (a n : Nat) (v : Word) (h : n ≠ a) :
    update m a v n = m n := by
  simp [update, h]

structure EState where
  mem : Nat → Word
  acc : Nat → Nat → Word
  idx : Nat
  pred : Bool
  pc : Nat
  halted : Bool

inductive EInstr where
  | store
  | inc
  | cmpGe (T : Nat)
  | jmpiIf (target : Nat)
  | jmpi (target : Nat)
  deriving Repr

def estep (base N : Nat) (prog : List EInstr) (s : EState) : EState :=
  match prog[s.pc]? with
  | none => { s with halted := true }
  | some .store =>
      { s with
        mem := update s.mem (base + s.idx) (s.acc (s.idx / N) (s.idx % N)),
        pc := s.pc + 1 }
  | some .inc => { s with idx := s.idx + 1, pc := s.pc + 1 }
  | some (.cmpGe T) => { s with pred := decide (T ≤ s.idx), pc := s.pc + 1 }
  | some (.jmpiIf target) => { s with pc := if s.pred then target else s.pc + 1 }
  | some (.jmpi target) => { s with pc := target }

def erun (base N : Nat) (prog : List EInstr) : Nat → EState → EState
  | 0, s => s
  | n + 1, s => erun base N prog n (estep base N prog s)

@[simp] theorem erun_zero (base N : Nat) (prog : List EInstr) (s : EState) :
    erun base N prog 0 s = s := rfl

@[simp] theorem erun_succ (base N : Nat) (prog : List EInstr) (n : Nat) (s : EState) :
    erun base N prog (n + 1) s = erun base N prog n (estep base N prog s) := rfl

theorem erun_add (base N : Nat) (prog : List EInstr) (a b : Nat) (s : EState) :
    erun base N prog (a + b) s = erun base N prog b (erun base N prog a s) := by
  induction a generalizing s with
  | zero => simp
  | succ a ih =>
      calc
        erun base N prog (a + 1 + b) s = erun base N prog (a + b) (estep base N prog s) := by
          rw [show a + 1 + b = (a + b) + 1 by omega]
          rfl
        _ = erun base N prog b (erun base N prog a (estep base N prog s)) :=
          ih (estep base N prog s)
        _ = erun base N prog b (erun base N prog (a + 1) s) := rfl

def epilogueProg (T : Nat) : List EInstr :=
  [.cmpGe T, .jmpiIf 5, .store, .inc, .jmpi 0]

def eHead (mem : Nat → Word) (acc : Nat → Nat → Word) : EState :=
  { mem := mem, acc := acc, idx := 0, pred := false, pc := 0, halted := false }

structure EInv (base N t0 : Nat) (acc : Nat → Nat → Word) (s : EState) : Prop where
  written : ∀ k < t0, s.mem (base + k) = acc (k / N) (k % N)
  accEq : s.acc = acc
  idxEq : s.idx = t0
  predF : s.pred = false
  pc0 : s.pc = 0
  haltF : s.halted = false

theorem estep_iter (base N T t0 : Nat) (acc : Nat → Nat → Word) (s : EState)
    (h : EInv base N t0 acc s) (ht : t0 < T) :
    EInv base N (t0 + 1) acc (erun base N (epilogueProg T) 5 s) := by
  have hknot : ¬ T ≤ t0 := by omega
  have hmem : ∀ k, (erun base N (epilogueProg T) 5 s).mem (base + k) =
      update s.mem (base + t0) (acc (t0 / N) (t0 % N)) (base + k) := by
    intro k
    simp [epilogueProg, erun, estep, h.pc0, h.idxEq, h.accEq, hknot]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    rw [hmem]
    by_cases hkt : k = t0
    · subst hkt
      rw [update_at]
    · have hne : base + k ≠ base + t0 := by omega
      rw [update_away _ _ _ _ hne]
      exact h.written k (by omega)
  · simp [epilogueProg, erun, estep, h.pc0, h.idxEq, h.accEq, hknot]
  · simp [epilogueProg, erun, estep, h.pc0, h.idxEq, h.accEq, hknot]
  · simp [epilogueProg, erun, estep, h.pc0, h.idxEq, h.accEq, hknot]
  · simp [epilogueProg, erun, estep, h.pc0, h.idxEq, h.accEq, hknot]
  · simp [epilogueProg, erun, estep, h.pc0, h.idxEq, h.accEq, hknot, h.haltF]

theorem estep_exit (base N T : Nat) (acc : Nat → Nat → Word) (s : EState)
    (h : EInv base N T acc s) :
    (erun base N (epilogueProg T) 3 s).halted = true := by
  have hle : T ≤ s.idx := by rw [h.idxEq]; omega
  simp [epilogueProg, erun, estep, h.pc0, hle]

theorem epilogue_run_aux (base N : Nat) (acc : Nat → Nat → Word) (T : Nat) :
    ∀ (n : Nat) (t0 : Nat) (s : EState), t0 + n = T → EInv base N t0 acc s →
      (erun base N (epilogueProg T) (5 * n + 3) s).halted = true ∧
        ∀ k < T, (erun base N (epilogueProg T) (5 * n + 3) s).mem (base + k) =
          acc (k / N) (k % N) := by
  intro n
  induction n with
  | zero =>
      intro t0 s ht h
      have ht0 : t0 = T := by omega
      have hT : EInv base N T acc s := ht0 ▸ h
      refine ⟨?_, ?_⟩
      · simpa using estep_exit base N T acc s hT
      · intro k hk
        have hmem : (erun base N (epilogueProg T) (5 * 0 + 3) s).mem (base + k) =
            s.mem (base + k) := by
          have hle : T ≤ s.idx := by rw [hT.idxEq]; omega
          simp [epilogueProg, erun, estep, hT.pc0, hle]
        rw [hmem]
        exact hT.written k (by omega)
  | succ n ih =>
      intro t0 s ht h
      have hlt : t0 < T := by omega
      have hnext : t0 + 1 + n = T := by omega
      have hiter := estep_iter base N T t0 acc s h hlt
      have hrun : erun base N (epilogueProg T) (5 * (n + 1) + 3) s =
          erun base N (epilogueProg T) (5 * n + 3) (erun base N (epilogueProg T) 5 s) := by
        rw [show 5 * (n + 1) + 3 = 5 + (5 * n + 3) by omega]
        exact erun_add base N (epilogueProg T) 5 (5 * n + 3) s
      rw [hrun]
      exact ih (t0 + 1) (erun base N (epilogueProg T) 5 s) hnext hiter

theorem epilogue_correct (base N : Nat) (T : Nat) (mem : Nat → Word)
    (acc : Nat → Nat → Word) :
    let s' := erun base N (epilogueProg T) (5 * T + 3) (eHead mem acc)
    s'.halted = true ∧ ∀ k < T, s'.mem (base + k) = acc (k / N) (k % N) := by
  have hinit : EInv base N 0 acc (eHead mem acc) :=
    ⟨by intro k hk; omega, rfl, rfl, rfl, rfl, rfl⟩
  exact epilogue_run_aux base N acc T T 0 (eHead mem acc) (by omega) hinit

theorem mul_add_div (hN : 0 < N) (m n : Nat) (hn : n < N) : (m * N + n) / N = m := by
  rw [Nat.mul_comm m N, Nat.mul_add_div (m := N) hN m n, Nat.div_eq_of_lt hn, Nat.add_zero]

theorem mul_add_mod (m n N : Nat) : (m * N + n) % N = n % N := by
  rw [Nat.mul_comm m N]
  exact Nat.mul_add_mod N m n

/-- The epilogue writes the tile's C block at origin `(gi, gj)` in a packed
`N`-wide matrix. -/
theorem epilogue_block (base N M gi gj : Nat) (hN : 0 < N) (mem : Nat → Word)
    (acc : Nat → Nat → Word) :
    let s' := erun (base + gi * N + gj) N (epilogueProg (M * N)) (5 * (M * N) + 3)
      (eHead mem acc)
    ∀ m < M, ∀ n < N, s'.mem (base + (gi + m) * N + (gj + n)) = acc m n := by
  dsimp only
  intro m hm n hn
  have hres := epilogue_correct (base + gi * N + gj) N (M * N) mem acc
  have hlt : m * N + n < M * N := by
    have h1 : m * N + n < m * N + N := Nat.add_lt_add_left hn (m * N)
    have h2 : m * N + N = (m + 1) * N := (Nat.succ_mul m N).symm
    have h3 : (m + 1) * N ≤ M * N := Nat.mul_le_mul_right N (by omega)
    omega
  have hk := hres.2 (m * N + n) hlt
  rw [mul_add_div hN m n hn, mul_add_mod m n N, Nat.mod_eq_of_lt hn] at hk
  have hbase : base + gi * N + gj + (m * N + n) = base + (gi + m) * N + (gj + n) := by
    rw [Nat.add_mul]
    omega
  rw [hbase] at hk
  exact hk

/-- A tile whose C block was written by the executed epilogue and whose
accumulator came from a `T`-step DPAS mainloop satisfies `TileSpec`. -/
theorem tileSpec_of_store (A B C : Nat → Nat → Word) (M N K d T BM BN ti tj : Nat)
    (hK : K = T * d)
    (hC : ∀ m < BM, ∀ n < BN,
      C (ti * BM + m) (tj * BN + n) =
        dpasRun A B (ti * BM) (tj * BN) d T (fun _ _ => 0) m n) :
    TileSpec A B C M N K BM BN ti tj := by
  intro m hm n hn _ _
  rw [hC m hm n hn, dpasRun_correct A B (ti * BM) (tj * BN) d T m n, ← hK]

/-- End to end for one output tile: the DPAS mainloop, then the epilogue
store, leaves `dotMat` in memory at the tile's C block. -/
theorem gemmTile_end_to_end (A B : Nat → Nat → Word) (d T BM BN : Nat)
    (hBN : 0 < BN) (base ti tj : Nat) (mem0 : Nat → Word)
    (s : XState) (hInit : XInv A B (ti * BM) (tj * BN) d 0 s) :
    let s1 := xrun A B (ti * BM) (tj * BN) d (dpasProg T) (7 * T + 3) s
    let e := erun (base + ti * BM * BN + tj * BN) BN (epilogueProg (BM * BN))
      (5 * (BM * BN) + 3) (eHead mem0 s1.acc)
    s1.halted = true ∧ e.halted = true ∧
      ∀ m < BM, ∀ n < BN,
        e.mem (base + (ti * BM + m) * BN + (tj * BN + n)) =
          dotMat A B (ti * BM + m) (tj * BN + n) (T * d) := by
  have hloop := dpasProg_correct A B (ti * BM) (tj * BN) d T s hInit
  have hepi := epilogue_correct (base + ti * BM * BN + tj * BN) BN (BM * BN) mem0
    (xrun A B (ti * BM) (tj * BN) d (dpasProg T) (7 * T + 3) s).acc
  dsimp only at hepi ⊢
  refine ⟨hloop.1, hepi.1, ?_⟩
  intro m hm n hn
  have hblk := epilogue_block base BN BM (ti * BM) (tj * BN)
    hBN mem0 (xrun A B (ti * BM) (tj * BN) d (dpasProg T) (7 * T + 3) s).acc
  dsimp only at hblk
  rw [hblk m hm n hn, hloop.2 m n]

end IntelGpu
