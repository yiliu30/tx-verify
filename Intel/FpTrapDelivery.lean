-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.FpExceptionFlags

@[expose] public section

/-!
# Trap delivery and exception masks

The flag model of `Intel.FpExceptionFlags` summarises the five IEEE exceptions
but leaves trap delivery and masks outside. This module adds them: a mask has
one bit per exception, `deliverTrap` raises a trap exactly when a masked
exception is set, and the sticky flags are carried by the trap.

The concrete overflow case is worked out: the maximum normal fp16 added to
itself raises overflow and inexact, so an overflow mask traps, an empty mask
does not, and an inexact-only mask also traps on the same addition.
-/

namespace IntelGpu

/-- Does any exception raised in `raised` match a bit of `mask`? -/
def Flags.anyOf (raised mask : Flags) : Bool :=
  (raised.invalid && mask.invalid) || (raised.divByZero && mask.divByZero) ||
  (raised.overflow && mask.overflow) || (raised.underflow && mask.underflow) ||
  (raised.inexact && mask.inexact)

/-- Is any exception raised at all? -/
def Flags.anyRaised (r : Flags) : Bool := r.anyOf Flags.all

/-- A delivered trap, carrying the raised flags. -/
structure FpTrap where
  flags : Flags
  deriving Repr, DecidableEq

/-- Deliver a trap when a masked exception is raised. -/
def deliverTrap (mask raised : Flags) : Option FpTrap :=
  if raised.anyOf mask then some ⟨raised⟩ else none

theorem anyOf_none (r : Flags) : r.anyOf Flags.none = false := by
  cases r with
  | mk i d o u x => simp [Flags.anyOf, Flags.none]

theorem anyOf_all (r : Flags) : r.anyOf Flags.all = r.anyRaised := by
  cases r with
  | mk i d o u x => simp [Flags.anyOf, Flags.anyRaised, Flags.all]

theorem deliverTrap_none_mask (r : Flags) : deliverTrap Flags.none r = none := by
  simp [deliverTrap, anyOf_none]

theorem deliverTrap_some (mask r : Flags) (h : r.anyOf mask = true) :
    deliverTrap mask r = some ⟨r⟩ := by
  simp [deliverTrap, h]

theorem deliverTrap_none (mask r : Flags) (h : r.anyOf mask = false) :
    deliverTrap mask r = none := by
  simp [deliverTrap, h]

/-- The max-normal fp16 word. -/
def maxNormal : Fp16Val := decodeFull 0x7BFF

/-- Max normal plus max normal raises overflow and inexact. -/
theorem addFlags_maxNormal :
    addFlags maxNormal maxNormal = Flags.overflowInexact := by decide

/-- An overflow-only exception mask. -/
def overflowMask : Flags :=
  { invalid := false, divByZero := false, overflow := true,
    underflow := false, inexact := false }

/-- The overflowing addition traps under an overflow mask. -/
theorem trap_overflow :
    deliverTrap overflowMask (addFlags maxNormal maxNormal) =
      some ⟨Flags.overflowInexact⟩ := by
  rw [addFlags_maxNormal]
  decide

/-- The same addition does not trap under an empty mask. -/
theorem no_trap_overflow :
    deliverTrap Flags.none (addFlags maxNormal maxNormal) = none :=
  deliverTrap_none_mask _

/-- An inexact-only mask also traps on the overflowing addition. -/
theorem trap_overflow_inexact :
    deliverTrap Flags.inexactOnly (addFlags maxNormal maxNormal) =
      some ⟨Flags.overflowInexact⟩ := by
  rw [addFlags_maxNormal]
  decide

/-- One plus one raises no exception and cannot trap. -/
theorem no_trap_one_add_one :
    deliverTrap Flags.all
      (addFlags (decodeFull 0x3C00) (decodeFull 0x3C00)) = none := by
  decide

end IntelGpu
