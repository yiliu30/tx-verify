-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.Fp16Value

@[expose] public section

/-!
# Zero times infinity is invalid

`Fp16Value.vstep` treats every finite operand times an infinity as an
infinity. IEEE-754 makes `0 * inf` an invalid operation and returns a NaN. This
module adds the refined step:

- `vstepIEEE`: NaN absorbs; `inf * inf` keeps the same sign and is NaN for
  opposite signs; a zero finite operand times an infinity is NaN; a non-zero
  finite operand times an infinity is an infinity.
- `vstepIEEE_zero_left` / `vstepIEEE_zero_right`: the invalid cases.
- `vstepIEEE_not_fin`: a non-finite accumulator never becomes finite.
- `foldValIEEE_fin`: all-finite operands still compute exactly the machine
  accumulation, so the refinement only changes the invalid non-finite cases.
- `vstep_zero_inf_old`: the old step returns an infinity there; the difference
  is exactly the invalid operation.

Payload policy: the refined invalid result carries payload `0`; the existing
NaN-payload propagation rules are unchanged.
-/

namespace IntelGpu

/-- A finite operand is zero exactly when its significand is zero. -/
def Fixed.isZero (v : Fixed) : Bool := v.mant == 0

/-- The refined value step with `0 * inf = NaN`. -/
def vstepIEEE (stepF : Fixed → Fixed → Fixed → Fixed) (acc x y : Fval) : Fval :=
  match acc, x, y with
  | .nan pl, _, _ => .nan pl
  | _, .nan pl, _ => .nan pl
  | _, _, .nan pl => .nan pl
  | .inf p, .inf r, _ => if p = r then .inf p else .nan 0
  | .inf p, .fin b, .inf _ => if b.mant = 0 then .nan 0 else .inf p
  | .fin _, .fin b, .inf r => if b.mant = 0 then .nan 0 else .inf r
  | .fin _, .inf p, .fin b => if b.mant = 0 then .nan 0 else .inf p
  | .inf p, _, _ => .inf p
  | _, .inf r, _ => .inf r
  | .fin c, .fin a, .fin b => .fin (stepF c a b)

/-- Value-depth accumulation with the refined step. -/
def foldValIEEE (stepF : Fixed → Fixed → Fixed → Fixed) (a b : Nat → Fval) (acc : Fval) :
    Nat → Fval
  | 0 => acc
  | n + 1 => foldValIEEE stepF a b (vstepIEEE stepF acc (a n) (b n)) n

theorem vstepIEEE_fin (stepF : Fixed → Fixed → Fixed → Fixed) (c a b : Fixed) :
    vstepIEEE stepF (.fin c) (.fin a) (.fin b) = .fin (stepF c a b) := rfl

theorem vstepIEEE_zero_left (stepF : Fixed → Fixed → Fixed → Fixed)
    (c z : Fixed) (hz : z.mant = 0) :
    vstepIEEE stepF (.fin c) (.fin z) (.inf true) = .nan 0 ∧
    vstepIEEE stepF (.fin c) (.fin z) (.inf false) = .nan 0 := by
  constructor <;> simp [vstepIEEE, hz]

theorem vstepIEEE_zero_right (stepF : Fixed → Fixed → Fixed → Fixed)
    (c z : Fixed) (hz : z.mant = 0) :
    vstepIEEE stepF (.fin c) (.inf true) (.fin z) = .nan 0 ∧
    vstepIEEE stepF (.fin c) (.inf false) (.fin z) = .nan 0 := by
  constructor <;> simp [vstepIEEE, hz]

theorem vstepIEEE_nonzero_left (stepF : Fixed → Fixed → Fixed → Fixed)
    (c z : Fixed) (r : Bool) (hz : z.mant ≠ 0) :
    vstepIEEE stepF (.fin c) (.fin z) (.inf r) = .inf r := by
  simp [vstepIEEE, hz]

theorem vstepIEEE_nonzero_right (stepF : Fixed → Fixed → Fixed → Fixed)
    (c z : Fixed) (p : Bool) (hz : z.mant ≠ 0) :
    vstepIEEE stepF (.fin c) (.inf p) (.fin z) = .inf p := by
  simp [vstepIEEE, hz]

theorem vstepIEEE_inf_same (stepF : Fixed → Fixed → Fixed → Fixed)
    (p : Bool) (b : Fixed) :
    vstepIEEE stepF (.inf p) (.inf p) (.fin b) = .inf p := by
  simp [vstepIEEE]

theorem vstepIEEE_inf_opposite (stepF : Fixed → Fixed → Fixed → Fixed)
    (p : Bool) (b : Fixed) :
    vstepIEEE stepF (.inf p) (.inf (!p)) (.fin b) = .nan 0 := by
  cases p <;> simp [vstepIEEE]

theorem vstepIEEE_nan_acc (stepF : Fixed → Fixed → Fixed → Fixed) (pl : Nat) (x y : Fval) :
    vstepIEEE stepF (.nan pl) x y = .nan pl := by
  cases x <;> cases y <;> rfl

theorem vstepIEEE_ne_fin_acc (stepF : Fixed → Fixed → Fixed → Fixed)
    (acc x y : Fval) (h : ¬ ∃ c, acc = .fin c) (v : Fixed) :
    vstepIEEE stepF acc x y ≠ .fin v := by
  rcases acc with pl | p | c
  · cases x <;> cases y <;> simp [vstepIEEE]
  · cases x <;> cases y <;> simp [vstepIEEE] <;> split <;> simp
  · exact absurd ⟨c, rfl⟩ h

theorem foldValIEEE_ne_fin (stepF : Fixed → Fixed → Fixed → Fixed)
    (a b : Nat → Fval) :
    ∀ (n : Nat) (acc : Fval), (¬ ∃ c, acc = .fin c) →
      ∀ v, foldValIEEE stepF a b acc n ≠ .fin v := by
  intro n
  induction n with
  | zero => intro acc h v hv; exact absurd ⟨v, hv⟩ h
  | succ n ih =>
      intro acc h v hv
      exact ih (vstepIEEE stepF acc (a n) (b n)) (by
        rintro ⟨c, hc⟩
        exact vstepIEEE_ne_fin_acc stepF acc (a n) (b n) h c hc) v hv

theorem foldValIEEE_fin (stepF : Fixed → Fixed → Fixed → Fixed)
    (a b : Nat → Fixed) (acc : Fixed) :
    ∀ n, foldValIEEE stepF (fun k => .fin (a k)) (fun k => .fin (b k)) (.fin acc) n =
      .fin (foldFixed stepF a b acc n) := by
  intro n
  induction n generalizing acc with
  | zero => rfl
  | succ n ih =>
      simp only [foldValIEEE, foldFixed, vstepIEEE_fin]
      exact ih (stepF acc (a n) (b n))

/-- The old step returns an infinity for `0 * inf`; the refinement is exactly
that invalid case. -/
theorem vstep_zero_inf_old (stepF : Fixed → Fixed → Fixed → Fixed)
    (c z : Fixed) (r : Bool) (_hz : z.mant = 0) :
    vstep stepF (.fin c) (.fin z) (.inf r) = .inf r := by
  simp [vstep]

end IntelGpu
