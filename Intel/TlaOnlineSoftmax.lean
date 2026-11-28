-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaSoftmax

@[expose] public section

/-!
# Online softmax over KV tiles

Flash attention keeps a running maximum `m`, denominator `l` and weighted
value `acc`, and rescales by `exp(m_old - m_new)` when a tile raises the
maximum. This module proves the fold invariant over `Rat`: after any prefix,
`l` and `acc` are the two-pass sums `sum exp(x - m)` and
`sum exp(x - m) * v` at the running `m`.

The rescaling step uses the exponential law
`exp a * exp b = exp (a + b)`, which is a separate contract from the MUFU
error budget. The final division by `l` is added with the epilogue stage.
-/

namespace IntelGpu

/-- The running softmax state. -/
structure OnlineState where
  m : Rat
  l : Rat
  acc : Rat
  deriving Repr, DecidableEq

/-- The two-pass denominator at a reference maximum. -/
def twoPassDen (e : Rat → Rat) (m : Rat) (ps : List (Rat × Rat)) : Rat :=
  (ps.map (fun p => e (p.1 - m))).sum

/-- The two-pass numerator (weighted values) at a reference maximum. -/
def twoPassNum (e : Rat → Rat) (m : Rat) (ps : List (Rat × Rat)) : Rat :=
  (ps.map (fun p => e (p.1 - m) * p.2)).sum

/-- One online-softmax update. -/
def onlineStep (e : Rat → Rat) (st : OnlineState) (p : Rat × Rat) : OnlineState :=
  let mNew := ratMax st.m p.1
  let alpha := e (st.m - mNew)
  let w := e (p.1 - mNew)
  ⟨mNew, alpha * st.l + w, alpha * st.acc + w * p.2⟩

/-- Fold the update over a tile. -/
def onlineFold (e : Rat → Rat) (st : OnlineState) (ps : List (Rat × Rat)) : OnlineState :=
  ps.foldl (onlineStep e) st

/-- The invariant: the state holds the two-pass sums at its own maximum. -/
def OnlineInv (e : Rat → Rat) (st : OnlineState) (ps : List (Rat × Rat)) : Prop :=
  st.l = twoPassDen e st.m ps ∧ st.acc = twoPassNum e st.m ps

/-- The exponential law gives the rescaling identity. -/
theorem exp_sub_mul (e : Rat → Rat)
    (hLaw : ∀ a b, e a * e b = e (a + b)) (a b c : Rat) :
    e (a - b) * e (b - c) = e (a - c) := by
  rw [hLaw]
  congr 1
  rw [Rat.sub_eq_add_neg, Rat.sub_eq_add_neg, Rat.sub_eq_add_neg]
  rw [Rat.add_assoc, ← Rat.add_assoc (-b) b (-c), Rat.neg_add_cancel, Rat.zero_add]

theorem sum_rescale_den (e : Rat → Rat)
    (hLaw : ∀ a b, e a * e b = e (a + b)) (mOld mNew : Rat)
    (ps : List (Rat × Rat)) :
    e (mOld - mNew) * twoPassDen e mOld ps = twoPassDen e mNew ps := by
  unfold twoPassDen
  rw [← sum_map_mul_left, List.map_map]
  simp only [Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  rw [Rat.mul_comm]
  exact exp_sub_mul e hLaw p.1 mOld mNew

theorem sum_rescale_num (e : Rat → Rat)
    (hLaw : ∀ a b, e a * e b = e (a + b)) (mOld mNew : Rat)
    (ps : List (Rat × Rat)) :
    e (mOld - mNew) * twoPassNum e mOld ps = twoPassNum e mNew ps := by
  unfold twoPassNum
  rw [← sum_map_mul_left, List.map_map]
  simp only [Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  rw [← Rat.mul_assoc, Rat.mul_comm (e (mOld - mNew)) (e (p.1 - mOld))]
  rw [exp_sub_mul e hLaw p.1 mOld mNew]

/-- One update preserves the invariant. -/
theorem onlineStep_spec (e : Rat → Rat)
    (hLaw : ∀ a b, e a * e b = e (a + b)) (st : OnlineState)
    (p : Rat × Rat) (ps : List (Rat × Rat)) (hinv : OnlineInv e st ps) :
    OnlineInv e (onlineStep e st p) (ps ++ [p]) := by
  obtain ⟨hl, ha⟩ := hinv
  constructor
  · unfold onlineStep
    dsimp only
    rw [hl, sum_rescale_den e hLaw st.m (ratMax st.m p.1) ps]
    unfold twoPassDen
    rw [List.map_append, List.sum_append]
    simp [Rat.add_zero]
  · unfold onlineStep
    dsimp only
    rw [ha, sum_rescale_num e hLaw st.m (ratMax st.m p.1) ps]
    unfold twoPassNum
    rw [List.map_append, List.sum_append]
    simp [Rat.add_zero]

/-- Folding a list of tiles preserves the invariant. -/
theorem onlineFold_spec (e : Rat → Rat)
    (hLaw : ∀ a b, e a * e b = e (a + b)) :
    ∀ (qs : List (Rat × Rat)) (st : OnlineState) (ps : List (Rat × Rat)),
      OnlineInv e st ps → OnlineInv e (onlineFold e st qs) (ps ++ qs)
  | [], st, ps, hinv => by simpa [onlineFold] using hinv
  | q :: qs, st, ps, hinv => by
      simp only [onlineFold, List.foldl_cons]
      have h1 := onlineStep_spec e hLaw st q ps hinv
      have h2 := onlineFold_spec e hLaw qs (onlineStep e st q) (ps ++ [q]) h1
      simpa [List.append_assoc, onlineFold] using h2

/-- The initial running state. -/
def onlineInit : OnlineState := ⟨0, 0, 0⟩

theorem onlineInit_inv (e : Rat → Rat) : OnlineInv e onlineInit [] := by
  simp [OnlineInv, onlineInit, twoPassDen, twoPassNum]

/-- The fold from the initial state holds the two-pass sums at its running
maximum. -/
theorem onlineFold_init_spec (e : Rat → Rat)
    (hLaw : ∀ a b, e a * e b = e (a + b)) (ps : List (Rat × Rat)) :
    OnlineInv e (onlineFold e onlineInit ps) ps :=
  onlineFold_spec e hLaw ps onlineInit [] (onlineInit_inv e)

/-- The running denominator equals the two-pass denominator. -/
theorem onlineFold_init_den (e : Rat → Rat)
    (hLaw : ∀ a b, e a * e b = e (a + b)) (ps : List (Rat × Rat)) :
    (onlineFold e onlineInit ps).l =
      twoPassDen e (onlineFold e onlineInit ps).m ps :=
  (onlineFold_init_spec e hLaw ps).1

/-- The running weighted value equals the two-pass numerator. -/
theorem onlineFold_init_num (e : Rat → Rat)
    (hLaw : ∀ a b, e a * e b = e (a + b)) (ps : List (Rat × Rat)) :
    (onlineFold e onlineInit ps).acc =
      twoPassNum e (onlineFold e onlineInit ps).m ps :=
  (onlineFold_init_spec e hLaw ps).2

end IntelGpu
