-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaOperandLoad
public import Intel.FmhaPrefillCoverage
public import Intel.TlaFmhaDpasBase

@[expose] public section

/-!
# FMHA load -> BF16 operand bridge

The GEMM load bridge relates a 16-register `load_block2d` window to the flat
tile reads. This module lifts it to the packed-BF16 reads (`bf16ReadA`,
`bf16ReadB`) and works out the `r46:16` V load at PC 1543, which feeds the
`r46` B operand of the PV atoms at PCs 1579-1582.
-/

namespace IntelGpu

/-- A 16-register load feeds the packed-BF16 B read. -/
theorem loadWindow_feeds_bf16ReadB (st : TlaState) (mem : TlaMem) (bti : Nat → Word)
    (b : TlaBlock2d) (base : Nat) (p : TlaState × TlaMem)
    (h : tlaBlock2dLoadW? st mem bti ⟨base, 16⟩ b = some p)
    (a : TlaAddr) (hp : parseTlaAddr b.addr = some a)
    (k n : Nat) (hk : k < 16) (hn : n < 8)
    (ha : b.exec.elementActive (bLane n k) = true) :
    bf16ReadB (flat p.1.regs) base k n =
      bf16Word (bf16Lo (mem.loadTile (a.effAddr st bti) (bLane n k))) := by
  unfold bf16ReadB
  rw [loadWindow_feeds_readTileB st mem bti b base p h a hp k n hk hn ha]

/-- A 31-register load feeds the packed-BF16 A read. -/
theorem loadWindow_feeds_bf16ReadA (st : TlaState) (mem : TlaMem) (bti : Nat → Word)
    (b : TlaBlock2d) (base : Nat) (p : TlaState × TlaMem)
    (h : tlaBlock2dLoadW? st mem bti ⟨base, 31⟩ b = some p)
    (a : TlaAddr) (hp : parseTlaAddr b.addr = some a)
    (m k : Nat) (hm : m < 8) (hk : k < 16)
    (ha : b.exec.elementActive (aLane m k) = true) :
    bf16ReadA (flat p.1.regs) base m k =
      bf16Word (bf16Lo (mem.loadTile (a.effAddr st bti) (aLane m k))) := by
  unfold bf16ReadA
  rw [readTileA_flat (rf := p.1.regs) (base := base) (m := m) (k := k) hm]
  exact congrArg (fun w => bf16Word (bf16Lo w))
    (loadWindow_feeds_readTileA st mem bti b base p h a hp m k hm hk ha)

/-- The V load at PC 1543 (`r46:16`). -/
def load1543 : TlaBlock2d :=
  ⟨"load_block2d.ugm.d16v.a64", ⟨1, 0, true⟩, "r46:16", "[r10:1]"⟩

set_option maxRecDepth 1000000 in
theorem parseLoad1543 :
    (fmhaParsedAt 1543).bind parseTlaBlock2dPlain = some load1543 := by
  decide

/-- PC 1543 feeds the `r46` BF16 B tile. -/
theorem load1543_feeds_bf16B (st : TlaState) (mem : TlaMem) (bti : Nat → Word)
    (p : TlaState × TlaMem) (h : tlaBlock2dLoadW? st mem bti ⟨46, 16⟩ load1543 = some p)
    (a : TlaAddr) (hp : parseTlaAddr load1543.addr = some a)
    (k n : Nat) (hk : k < 16) (hn : n < 8)
    (ha : load1543.exec.elementActive (bLane n k) = true) :
    bf16ReadB (flat p.1.regs) 46 k n =
      bf16Word (bf16Lo (mem.loadTile (a.effAddr st bti) (bLane n k))) :=
  loadWindow_feeds_bf16ReadB st mem bti load1543 46 p h a hp k n hk hn ha

end IntelGpu
