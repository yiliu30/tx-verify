-- SPDX-License-Identifier: Apache-2.0
module

public import Std

@[expose] public section

/-!
# A minimal Intel-Xe / IGC semantic core

This module models the subset needed by a single-lane `add_one` kernel:
word-addressed global memory, 32-bit data registers, 64-bit address
registers, `load.ugm.d32.a64`, `add`, `store.ugm.d32.a64`, and EOT.

It is deliberately not a full Xe ISA model: SIMD masks, GRF regions,
predicates, scoreboards, SEND, SLM, barriers, and the launch ABI are
outside this first fragment.

The memory abstraction is word-addressed (one 32-bit word per address) and
assumes the modeled `d32` access is 4-byte aligned. Byte-level endianness and
unaligned accesses are deferred to a later refinement.
-/

namespace IntelGpu

abbrev Word := BitVec 32
abbrev Addr := BitVec 64

structure State where
  regs : Nat → Word
  addrRegs : Nat → Addr
  mem : Nat → Word
  halted : Bool

inductive Instr where
  | load32 (dst addrReg : Nat)
  | addImm (dst src : Nat) (imm : Word)
  | addAddrImm (dst : Nat) (imm : Addr)
  | add (dst src1 src2 : Nat)
  | mul (dst src1 src2 : Nat)
  | store32 (addrReg src : Nat)
  | eot
  deriving Repr

/-- A 32-bit load at a 4-byte-aligned byte address. -/
def load32 (m : Nat → Word) (byteAddr : Nat) : Word :=
  m (byteAddr / 4)

/-- Replace the word at index `a`. -/
def update (m : Nat → Word) (a : Nat) (v : Word) : Nat → Word :=
  fun n => if n = a then v else m n

/-- A 32-bit store at a 4-byte-aligned byte address. -/
def store32 (m : Nat → Word) (byteAddr : Nat) (v : Word) : Nat → Word :=
  update m (byteAddr / 4) v

theorem load32_store32_same (m : Nat → Word) (a : Nat) (v : Word) :
    load32 (store32 m a v) a = v := by
  simp [load32, store32, update]

theorem store32_frame (m : Nat → Word) (a : Nat) (v : Word) (n : Nat)
    (h : n ≠ a / 4) : store32 m a v n = m n := by
  simp [store32, update, h]

def step : State → Instr → State
  | s, .load32 dst addrReg =>
      { s with regs := fun r =>
          if r = dst then load32 s.mem (s.addrRegs addrReg).toNat else s.regs r }
  | s, .addImm dst src imm =>
      { s with regs := fun r => if r = dst then s.regs src + imm else s.regs r }
  | s, .addAddrImm dst imm =>
      { s with addrRegs := fun r =>
          if r = dst then s.addrRegs dst + imm else s.addrRegs r }
  | s, .add dst src1 src2 =>
      { s with regs := fun r =>
          if r = dst then s.regs src1 + s.regs src2 else s.regs r }
  | s, .mul dst src1 src2 =>
      { s with regs := fun r =>
          if r = dst then s.regs src1 * s.regs src2 else s.regs r }
  | s, .store32 addrReg src =>
      { s with mem := store32 s.mem (s.addrRegs addrReg).toNat (s.regs src) }
  | s, .eot => { s with halted := true }

def run (s : State) (is : List Instr) : State :=
  is.foldl step s

end IntelGpu
