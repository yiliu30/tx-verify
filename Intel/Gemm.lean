-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.Asm

@[expose] public section

/-!
# GEMM loop invariant

The modeled integer GEMM has the expected SIMD32 lambda loop:

```
load.ugm.d32.a64  A[i,k]
load.ugm.d32.a64  B[k,j]
mul/add           sum += A[i,k] * B[k,j]
cmp/branch        k < K
store.ugm.d32.a64 C[i,j]
```

This file isolates the mathematical loop invariant.  Connecting the IGC
loads, multiply, compare and branch to this invariant is the next step.
-/

namespace IntelGpu

/-- Exact integer dot product of row `i` of A and column `j` of B. -/
def dot (A B : Nat → Nat → Int) (i j : Nat) : Nat → Int
  | 0 => 0
  | k + 1 => dot A B i j k + A i k * B k j

structure GemmLoop where
  acc : Int
  k : Nat

def gemmStep (A B : Nat → Nat → Int) (i j : Nat) (s : GemmLoop) : GemmLoop :=
  { acc := s.acc + A i s.k * B s.k j, k := s.k + 1 }

def gemmRun (A B : Nat → Nat → Int) (i j : Nat) : Nat → GemmLoop
  | 0 => { acc := 0, k := 0 }
  | n + 1 => gemmStep A B i j (gemmRun A B i j n)

@[simp] theorem gemmRun_k (A B : Nat → Nat → Int) (i j n : Nat) :
    (gemmRun A B i j n).k = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [gemmRun, gemmStep, ih]

theorem gemmRun_acc (A B : Nat → Nat → Int) (i j n : Nat) :
    (gemmRun A B i j n).acc = dot A B i j n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [gemmRun, gemmStep, dot, ih]

/-- The GEMM specification: every output element is the exact dot product. -/
def GemmSpec (A B C : Nat → Nat → Int) (M N K : Nat) : Prop :=
  ∀ i < M, ∀ j < N, C i j = dot A B i j K

end IntelGpu
