-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.FpTrapDelivery

@[expose] public section

/-!
# Trap delivery and architectural halting

`Intel.FpTrapDelivery` decides whether a mask delivers a trap. This module
gives delivery its architectural effect: a trapping operation halts the
machine, records the trap, and does not write its destination; an untrapped
operation writes normally. Once halted, further writes and steps are no-ops.

The concrete overflow case is carried over: with the overflow mask, max normal
plus max normal traps and `r0` keeps its old value; without the mask, `r0`
receives the sum.
-/

namespace IntelGpu

/-- A scalar machine with a halt flag and a pending trap. -/
structure FpMachine where
  regs : Nat → Word
  pc : Nat
  halted : Bool
  trap : Option FpTrap

def FpMachine.halt (m : FpMachine) (t : FpTrap) : FpMachine :=
  { m with halted := true, trap := some t }

/-- A guarded register write; halted machines ignore writes. -/
def FpMachine.write (m : FpMachine) (r : Nat) (v : Word) : FpMachine :=
  if m.halted then m
  else { m with regs := fun r' => if r' = r then v else m.regs r' }

/-- One trapping add: deliver the trap or write the wrapped sum. -/
def FpMachine.stepAdd (m : FpMachine) (dst : Nat) (x y : Word)
    (flags mask : Flags) : FpMachine :=
  match deliverTrap mask flags with
  | some t => m.halt t
  | none => m.write dst (x + y)

/-- A trapping add halts the machine, records the trap and leaves the
destination unchanged. -/
theorem stepAdd_traps (m : FpMachine) (dst : Nat) (x y : Word)
    (flags mask : Flags) (t : FpTrap) (h : deliverTrap mask flags = some t) :
    (m.stepAdd dst x y flags mask).halted = true ∧
      (m.stepAdd dst x y flags mask).trap = some t ∧
      (m.stepAdd dst x y flags mask).regs dst = m.regs dst := by
  unfold FpMachine.stepAdd
  rw [h]
  exact ⟨rfl, rfl, rfl⟩

/-- An untrapped add writes the wrapped sum and stays running. -/
theorem stepAdd_no_trap (m : FpMachine) (dst : Nat) (x y : Word)
    (flags mask : Flags) (hm : m.halted = false)
    (h : deliverTrap mask flags = none) :
    (m.stepAdd dst x y flags mask).halted = false ∧
      (m.stepAdd dst x y flags mask).regs dst = x + y := by
  unfold FpMachine.stepAdd
  rw [h]
  unfold FpMachine.write
  simp [hm]

/-- Halting is absorbing for writes. -/
theorem halted_write (m : FpMachine) (t : FpTrap) (r : Nat) (v : Word) :
    (m.halt t).write r v = m.halt t := by
  unfold FpMachine.write FpMachine.halt
  simp

/-- The maximum-normal overflow pattern with an overflow mask traps. -/
theorem overflow_trap_halts (m : FpMachine) :
    (m.stepAdd 0 0 1 Flags.overflowInexact overflowMask).halted = true ∧
      (m.stepAdd 0 0 1 Flags.overflowInexact overflowMask).regs 0 = m.regs 0 := by
  have h : deliverTrap overflowMask Flags.overflowInexact =
      some ⟨Flags.overflowInexact⟩ := by decide
  exact ⟨(stepAdd_traps m 0 0 1 Flags.overflowInexact overflowMask _ h).1,
    (stepAdd_traps m 0 0 1 Flags.overflowInexact overflowMask _ h).2.2⟩

/-- The same pattern without a mask writes the sum. -/
theorem overflow_no_mask_writes (m : FpMachine) (hm : m.halted = false) :
    (m.stepAdd 0 0 1 Flags.overflowInexact Flags.none).halted = false ∧
      (m.stepAdd 0 0 1 Flags.overflowInexact Flags.none).regs 0 = 1 := by
  have h : deliverTrap Flags.none Flags.overflowInexact = none := deliverTrap_none_mask _
  exact ⟨(stepAdd_no_trap m 0 0 1 Flags.overflowInexact Flags.none hm h).1,
    (stepAdd_no_trap m 0 0 1 Flags.overflowInexact Flags.none hm h).2⟩

end IntelGpu
