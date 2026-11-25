-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaInstance

@[expose] public section

/-!
# DPAS at instruction granularity

Assumption 5 in the ledger says DPAS is modelled as one tile operation. This
module refines that: a tile DPAS of depth `d` peels atoms off the front, so the
tile operation is not a primitive.

- `dpasSlab_split`: a slab of depth `atom + rest` is one atom plus a slab over
  the operands shifted by `atom`.
- `dpasSlab_two_atoms`: the SYCL-TLA shape — a `K` tile of depth `32` is two
  atom instructions of depth `16`.

The operand shift is the content: after an atom, the next instruction reads the
operands `atom` columns further along, which is what the kernel's register
rotation does.
-/

namespace IntelGpu

/-- A slab is one atom plus the rest, over shifted operands. -/
theorem dpasSlab_split (dA rest : Nat) (A B : Nat → Nat → Word) (m n : Nat) :
    dpasSlab (dA + rest) A B m n =
      dpasSlab dA A B m n +
        dpasSlab rest (fun k m' => A (k + dA) m') (fun k n' => B (k + dA) n') m n := by
  induction dA generalizing A B with
  | zero =>
      simp [dpasSlab]
  | succ dA ih =>
      have hidx : (dA + 1) + rest = (dA + rest) + 1 := by omega
      rw [hidx, dpasSlab, ih (fun k m' => A (k + 1) m') (fun k n' => B (k + 1) n'), dpasSlab]
      have hA : (fun k m' => (fun k' m'' => A (k' + 1) m'') (k + dA) m') =
          fun k m' => A (k + (dA + 1)) m' := by
        funext k m'
        simp only []
        congr 1
      have hB : (fun k n' => (fun k' n'' => B (k' + 1) n'') (k + dA) n') =
          fun k n' => B (k + (dA + 1)) n' := by
        funext k n'
        simp only []
        congr 1
      rw [hA, hB]
      ac_rfl

/-- The SYCL-TLA `K` tile: depth `32` is two atom instructions of depth `16`. -/
theorem dpasSlab_two_atoms (A B : Nat → Nat → Word) (m n : Nat) :
    dpasSlab 32 A B m n =
      dpasSlab 16 A B m n +
        dpasSlab 16 (fun k m' => A (k + 16) m') (fun k n' => B (k + 16) n') m n := by
  have h := dpasSlab_split 16 16 A B m n
  rw [show (16 : Nat) + 16 = 32 by omega] at h
  exact h

end IntelGpu
