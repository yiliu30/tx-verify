-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.RealDpas

@[expose] public section

/-!
# Packed DPAS operands

The real FMHA instruction is `dpas.8x8 (16|M0) r383:f null:f r39:hf8
r335.0:hf8`. Its A, B and C operands are not plain matrices: they occupy GRFs
according to the vISA DPAS layout. For an fp8 `8x8x32` atom the ISA specifies:

- A (Src2) and C (Dst/Src0) are row-major in the register file;
- B (Src1) is column-packed: depth `k` is byte `k % 4` of the dword at
  column `n` in GRF `k / 4` after the B base.

`fmhaPackedA`, `fmhaPackedB` and `fmhaPackedC` express those addresses.
`fmhaRealPackedAtom_correct` connects the real operand bases to the already
proved `fmhaAtom_correct`; it does not claim that the compiler chose these
bases (that is recorded from the dump).

The GRF width is a parameter because the ISA uses 8 dwords before PVC and 16
on PVC and later. The real FMHA kernel is modelled with 16.
-/

namespace IntelGpu

/-- A byte lane of a 32-bit register element. -/
def fp8Lane (dw : Word) (b : Nat) : Word :=
  (dw >>> (8 * b)) &&& 0xFF

/-- Address of a row-major fp8 A element: register, dword and byte lane. -/
def fmhaAAddr (base grfDwords m k : Nat) : Nat × Nat × Nat :=
  let linear := m * 32 + k
  let dw := linear / 4
  (base + dw / grfDwords, dw % grfDwords, linear % 4)

/-- Row-major fp8 A: a row is 32 bytes, so `m*32 + k` selects the byte. -/
def fmhaPackedA (regs : Nat → Nat → Word) (base grfDwords : Nat)
    (m k : Nat) : Word :=
  let a := fmhaAAddr base grfDwords m k
  fp8Lane (regs a.1 a.2.1) a.2.2

/-- Address of a column-packed fp8 B element. -/
def fmhaBAddr (base dword k n : Nat) : Nat × Nat × Nat :=
  (base + k / 4, dword + n, k % 4)

/-- Column-packed fp8 B: column `n` lives in dword `n`, depth `k` in byte
`k % 4`, and successive four-depth groups advance one GRF. -/
def fmhaPackedB (regs : Nat → Nat → Word) (base dword : Nat)
    (k n : Nat) : Word :=
  let a := fmhaBAddr base dword k n
  fp8Lane (regs a.1 a.2.1) a.2.2

/-- Address of a row-major f32 C element: register and dword. -/
def fmhaCAddr (base grfDwords m n : Nat) : Nat × Nat :=
  let linear := m * 8 + n
  (base + linear / grfDwords, linear % grfDwords)

/-- Row-major f32 C: `N = 8` dwords per row. -/
def fmhaPackedC (regs : Nat → Nat → Word) (base grfDwords : Nat)
    (m n : Nat) : Word :=
  let a := fmhaCAddr base grfDwords m n
  regs a.1 a.2

/-- The A operand's first byte comes from the base register's byte zero. -/
theorem fmhaPackedA_zero (regs : Nat → Nat → Word) (base grfDwords : Nat) :
    fmhaPackedA regs base grfDwords 0 0 = fp8Lane (regs base 0) 0 := by
  simp [fmhaPackedA, fmhaAAddr]

/-- The B operand's first byte comes from the base register's dword zero. -/
theorem fmhaPackedB_zero (regs : Nat → Nat → Word) (base dword : Nat) :
    fmhaPackedB regs base dword 0 0 = fp8Lane (regs base dword) 0 := by
  simp [fmhaPackedB, fmhaBAddr]

/-- The C operand's first element is the base register's element zero. -/
theorem fmhaPackedC_zero (regs : Nat → Nat → Word) (base grfDwords : Nat) :
    fmhaPackedC regs base grfDwords 0 0 = regs base 0 := by
  simp [fmhaPackedC, fmhaCAddr]

/-- The decoded FMHA operand bases: A = r39, B = r335.0, C = r383. -/
def fmhaRealA (regs : Nat → Nat → Word) : Nat → Nat → Word :=
  fmhaPackedA regs 39 16

def fmhaRealB (regs : Nat → Nat → Word) : Nat → Nat → Word :=
  fmhaPackedB regs 335 0

def fmhaRealC (regs : Nat → Nat → Word) : Nat → Nat → Word :=
  fmhaPackedC regs 383 16

/-- The real packed operands feed the depth-32 8x8 atom proved in stage 88. -/
theorem fmhaRealPackedAtom_correct (regs : Nat → Nat → Word) (i j m n : Nat) :
    fmhaAtom (fmhaRealA regs) (fmhaRealB regs) (fmhaRealC regs) i j m n =
      fmhaRealC regs (i + m) (j + n) +
        dotMatFrom (fmhaRealA regs) (fmhaRealB regs) (i + m) (j + n) 0 32 := by
  exact fmhaAtom_correct (fmhaRealA regs) (fmhaRealB regs) (fmhaRealC regs) i j m n

/-- A concrete B address check: depth 7, column 3 is byte 3 of dword 3 in
GRF 1 after the base. -/
theorem fmhaRealB_address (regs : Nat → Nat → Word) :
    fmhaRealB regs 7 3 = fp8Lane (regs 336 3) 3 := by
  simp [fmhaRealB, fmhaPackedB, fmhaBAddr]

/-- Distinct depth/column pairs have distinct packed B addresses. -/
theorem fmhaBAddr_injective (base dword k1 k2 n1 n2 : Nat)
    (h : fmhaBAddr base dword k1 n1 = fmhaBAddr base dword k2 n2) :
    k1 = k2 ∧ n1 = n2 := by
  simp [fmhaBAddr] at h
  obtain ⟨hreg, hdw, hbyte⟩ := h
  have hk : k1 = k2 := by omega
  have hn : n1 = n2 := by omega
  exact ⟨hk, hn⟩

/-- Distinct A depths have distinct 16-dword register addresses. -/
theorem fmhaAAddr_injective16 (base m1 k1 m2 k2 : Nat)
    (hk1 : k1 < 32) (hk2 : k2 < 32)
    (h : fmhaAAddr base 16 m1 k1 = fmhaAAddr base 16 m2 k2) :
    m1 = m2 ∧ k1 = k2 := by
  simp [fmhaAAddr] at h
  obtain ⟨_hreg, _hdw, _hbyte⟩ := h
  have hlin : m1 * 32 + k1 = m2 * 32 + k2 := by omega
  omega

/-- Distinct C columns have distinct 16-dword register addresses. -/
theorem fmhaCAddr_injective16 (base m1 n1 m2 n2 : Nat)
    (hn1 : n1 < 8) (hn2 : n2 < 8)
    (h : fmhaCAddr base 16 m1 n1 = fmhaCAddr base 16 m2 n2) :
    m1 = m2 ∧ n1 = n2 := by
  simp [fmhaCAddr] at h
  obtain ⟨_hreg, _hdw⟩ := h
  have hlin : m1 * 8 + n1 = m2 * 8 + n2 := by omega
  omega

end IntelGpu
