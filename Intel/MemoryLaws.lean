-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.Asm

@[expose] public section

/-!
# Memory-model laws for aligned 32-bit accesses

Stage 1 defines `load32` and `store32` and proves only what `add_one` needed.
Every later frame argument re-derives the rest, so this module collects the
laws once:

- `store32_store32_same`: overwriting the same address twice keeps the last.
- `store32_store32_commute`: stores at different addresses commute.
- `load32_store32_same` / `load32_store32_other`: a load sees its own store and
  nothing else.
- `store32_eq_self`: storing a value the memory already holds is a no-op.

The abstraction stays what stage 1 said it is: one 32-bit word per aligned
address, word-addressed underneath.
-/

namespace IntelGpu

theorem store32_store32_same (m : Nat → Word) (a : Nat) (v w : Word) :
    store32 (store32 m a v) a w = store32 m a w := by
  funext n
  by_cases h : n = a / 4 <;> simp [store32, update, h]

theorem store32_store32_commute (m : Nat → Word) (a b : Nat) (v w : Word)
    (h : a / 4 ≠ b / 4) :
    store32 (store32 m a v) b w = store32 (store32 m b w) a v := by
  funext n
  simp only [store32, update]
  by_cases ha : n = a / 4 <;> by_cases hb : n = b / 4 <;> simp_all

theorem load32_store32_other (m : Nat → Word) (a b : Nat) (v : Word) (h : a / 4 ≠ b / 4) :
    load32 (store32 m b v) a = load32 m a := by
  simp [load32, store32, update, h]

theorem store32_eq_self (m : Nat → Word) (a : Nat) :
    store32 m a (load32 m a) = m := by
  funext n
  simp only [store32, update, load32]
  by_cases h : n = a / 4 <;> simp_all

/-- A store followed by a load of the same aligned address. -/
example (m : Nat → Word) (a : Nat) (v : Word) :
    load32 (store32 m a v) a = v := load32_store32_same m a v

end IntelGpu
