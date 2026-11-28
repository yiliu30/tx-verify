-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.Asm
public import Std.Tactic.BVDecide
public meta import Std.Tactic.BVDecide.Reflect

@[expose] public section

/-!
# Dword storage and qword views

The loop vector add stores one 64-bit id per lane in `V0059` and reads the same
physical registers as dwords through `V0061`. A slot-per-element model cannot
express that view. This module gives the minimal foundation for a dword-level
register file and its qword view.

`DRegs` is a dword-addressed register file. `qwordOf` packs two adjacent dwords
into a 64-bit value; `setQword` splits a 64-bit value back into the pair. The
lemmas prove the round trips and the frame property for unrelated dwords.
-/

namespace IntelGpu

abbrev DRegs := Nat → Word

/-- The 64-bit value formed from dwords `2*i` and `2*i+1`. -/
def qwordOf (r : DRegs) (i : Nat) : Addr :=
  (r (2 * i)).zeroExtend 64 ||| ((r (2 * i + 1)).zeroExtend 64 <<< 32)

/-- Write one dword. -/
def setDword (r : DRegs) (i : Nat) (w : Word) : DRegs :=
  fun j => if j = i then w else r j

/-- Write one qword as its low and high dwords. -/
def setQword (r : DRegs) (i : Nat) (v : Addr) : DRegs :=
  setDword (setDword r (2 * i) (v.truncate 32)) (2 * i + 1) ((v >>> 32).truncate 32)

theorem setDword_same (r : DRegs) (i : Nat) (w : Word) :
    setDword r i w i = w := by
  simp [setDword]

theorem setDword_other (r : DRegs) (i j : Nat) (w : Word) (h : j ≠ i) :
    setDword r i w j = r j := by
  simp [setDword, h]

attribute [simp] setDword_same setDword_other

theorem setQword_low (r : DRegs) (i : Nat) (v : Addr) :
    setQword r i v (2 * i) = v.truncate 32 := by
  simp [setQword]

theorem setQword_high (r : DRegs) (i : Nat) (v : Addr) :
    setQword r i v (2 * i + 1) = (v >>> 32).truncate 32 := by
  simp [setQword]

attribute [simp] setQword_low setQword_high

theorem qwordOf_setQword (r : DRegs) (i : Nat) (v : Addr) :
    qwordOf (setQword r i v) i = v := by
  simp [qwordOf, setQword, setDword]
  bv_decide

theorem qwordOf_setDword_other (r : DRegs) (i j : Nat) (w : Word)
    (h1 : j ≠ 2 * i) (h2 : j ≠ 2 * i + 1) :
    qwordOf (setDword r j w) i = qwordOf r i := by
  have h1' : 2 * i ≠ j := by omega
  have h2' : 2 * i + 1 ≠ j := by omega
  unfold qwordOf
  simp [setDword, h1', h2']

end IntelGpu
