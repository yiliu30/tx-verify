-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.Dpas

@[expose] public section

/-!
# Rounding contract and accumulation error

Everything up to stage 26 computes in exact integers: `Word` arithmetic with no
rounding. Real GEMM hardware does not — fp16/bf16 operands and fp32
accumulators round at every multiply-add — so an exactness statement is the
wrong shape for a real kernel.

This module supplies the standard shape instead: a per-step rounding contract
plus an accumulation bound.

- `accDot` / `maccDot`: the same depth-ordered accumulation, exactly and on
  the machine.
- `maccDot_error`: if every machine step is within `eps` of the exact
  multiply-add, then `n` steps are within `n * eps`.
- `maccDot_zero_error`: with no rounding error the machine result *is* the
  exact result.
- `dpas_chain_error`: the depth-`T * d` bound for a DPAS-shaped chain, so the
  error of a tile grows with accumulation depth, not with tile count.

The scaling is fixed point: values are integers in a common unit, so `eps` is a
number of units. For fp16 inputs with fp32 accumulation, `eps` is one fp32 ulp
of the accumulator at the working magnitude.

The contract `hstep` is the hardware assumption. It is stated, not derived:
deriving it needs bit-level fp16/fp32 semantics, which is a separate
development.
-/

namespace IntelGpu

/-- Exact depth-ordered accumulation. -/
def accDot (a b : Nat → Int) (acc : Int) : Nat → Int
  | 0 => acc
  | n + 1 => accDot a b (acc + a n * b n) n

/-- The same accumulation with an abstract machine step. -/
def maccDot (step : Int → Int → Int → Int) (a b : Nat → Int) (acc : Int) : Nat → Int
  | 0 => acc
  | n + 1 => maccDot step a b (step acc (a n) (b n)) n

theorem accDot_eq (a b : Nat → Int) (acc : Int) :
    ∀ n, accDot a b acc n = acc + accDot a b 0 n := by
  intro n
  induction n generalizing acc with
  | zero => simp [accDot]
  | succ n ih =>
      simp only [accDot]
      rw [ih (acc + a n * b n), ih (0 + a n * b n)]
      omega

/-- Error accumulation: a per-step contract of `eps` bounds `n` steps by
`n * eps`. -/
theorem maccDot_error (step : Int → Int → Int → Int) (eps : Nat)
    (hstep : ∀ c x y, (step c x y - (c + x * y)).natAbs ≤ eps) :
    ∀ (n : Nat) (acc : Int) (a b : Nat → Int),
      (maccDot step a b acc n - accDot a b acc n).natAbs ≤ n * eps := by
  intro n
  induction n with
  | zero => intro acc a b; simp [maccDot, accDot]
  | succ n ih =>
      intro acc a b
      simp only [maccDot, accDot]
      have hstepn := hstep acc (a n) (b n)
      have hih := ih (step acc (a n) (b n)) a b
      have h1 : accDot a b (step acc (a n) (b n)) n
          = step acc (a n) (b n) + accDot a b 0 n := accDot_eq a b _ n
      have h2 : accDot a b (acc + a n * b n) n
          = (acc + a n * b n) + accDot a b 0 n := accDot_eq a b _ n
      have hsplit : maccDot step a b (step acc (a n) (b n)) n
            - accDot a b (acc + a n * b n) n =
          (maccDot step a b (step acc (a n) (b n)) n
            - accDot a b (step acc (a n) (b n)) n)
          + (step acc (a n) (b n) - (acc + a n * b n)) := by
        rw [h1, h2]
        omega
      rw [hsplit]
      have htri : ((maccDot step a b (step acc (a n) (b n)) n
            - accDot a b (step acc (a n) (b n)) n)
          + (step acc (a n) (b n) - (acc + a n * b n))).natAbs
          ≤ (maccDot step a b (step acc (a n) (b n)) n
            - accDot a b (step acc (a n) (b n)) n).natAbs
            + (step acc (a n) (b n) - (acc + a n * b n)).natAbs :=
        Int.natAbs_add_le _ _
      have hsum : (maccDot step a b (step acc (a n) (b n)) n
            - accDot a b (step acc (a n) (b n)) n).natAbs
          + (step acc (a n) (b n) - (acc + a n * b n)).natAbs ≤ n * eps + eps :=
        Nat.add_le_add hih hstepn
      have hstepEq : n * eps + eps = (n + 1) * eps := (Nat.succ_mul n eps).symm
      exact Nat.le_trans htri (Nat.le_trans hsum (Nat.le_of_eq hstepEq))

/-- With no rounding error, the machine accumulation *is* the exact one. -/
theorem maccDot_zero_error (step : Int → Int → Int → Int)
    (hstep : ∀ c x y, step c x y = c + x * y) :
    ∀ (n : Nat) (acc : Int) (a b : Nat → Int),
      maccDot step a b acc n = accDot a b acc n := by
  intro n
  induction n with
  | zero => intro acc a b; rfl
  | succ n ih =>
      intro acc a b
      simp only [maccDot, accDot, hstep]
      exact ih _ a b

/-- A DPAS-shaped chain of `T` slabs, each `d` deep, has error at most
`T * d * eps`: it grows with accumulation depth, not with the number of
tiles. -/
theorem dpas_chain_error (step : Int → Int → Int → Int) (eps : Nat)
    (hstep : ∀ c x y, (step c x y - (c + x * y)).natAbs ≤ eps)
    (T d : Nat) (acc : Int) (a b : Nat → Int) :
    (maccDot step a b acc (T * d) - accDot a b acc (T * d)).natAbs ≤ T * d * eps :=
  maccDot_error step eps hstep (T * d) acc a b

/-- Signed interpretation of a 32-bit word, for stating the contract at the
word level. -/
def toInt (w : Word) : Int :=
  if w.toNat < 2 ^ 31 then (w.toNat : Int) else (w.toNat : Int) - 2 ^ 32

end IntelGpu
