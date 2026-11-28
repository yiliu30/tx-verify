-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaOperandLoad
public import Intel.TlaFmhaLoad
public import Intel.Mainloop
public import Intel.FmhaPrefillCoverage
public import Intel.TlaFmhaDpasBase

@[expose] public section

/-!
# Physical 8x8x16 BF16 operand layout

This module follows the Xe DPAS atom traits in CUTE
(`mma_traits_xe.hpp`): the A fragment is M x K row-major with VNNI-packed K
(two BF16 per dword), the B fragment is K x N VNNI-packed, and C is
`readTileC`. Concretely, for a BF16 `dpas.8x8 (16|M0)`:

* A: `A(m,k) = half k%2 of rf (base+m) (k/2)` (8 registers, one row each);
* B: `B(k,n) = half k%2 of rf (base+n) (k/2)` (8 registers, one column each);
* C: `C(m,n) = rf (acc+m) n` (8 registers, `readTileC`).

The load bridges show that a 4-register load fills four A rows and a
16-register load fills two 8-register B tiles.
-/

namespace IntelGpu

/-- Select the low/high BF16 half of a packed dword for VNNI depth `k`. -/
def bf16Half (dw : Word) (k : Nat) : Word :=
  if k % 2 = 0 then bf16Word (bf16Lo dw) else bf16Word (bf16Hi dw)

/-- Physical A read: row per register, VNNI-packed K. -/
def readA16 (rf : RegFile) (base : Nat) (m k : Nat) : Word :=
  bf16Half (rf (base + m) (k / 2)) k

/-- Physical B read: column per register, VNNI-packed K. -/
def readB16 (rf : RegFile) (base : Nat) (k n : Nat) : Word :=
  bf16Half (rf (base + n) (k / 2)) k

/-- The physical BF16 slab of one atom. `dpasSlab` passes the depth first,
so the A read is wrapped to keep row/depth in the physical order. -/
def physSlab (rf : RegFile) (d : FmhaDpas) (m n : Nat) : Word :=
  dpasSlab 16 (fun k m' => readA16 rf d.srcA m' k)
    (fun k n' => readB16 rf d.srcB k n') m n

/-- Execute one atom with the physical layout. -/
def physStep (rf : RegFile) (d : FmhaDpas) : RegFile :=
  writeTileC rf d.acc0 (fun m n => readTileC rf d.acc0 m n + physSlab rf d m n)

theorem physStep_acc0 (rf : RegFile) (d : FmhaDpas) (m n : Nat)
    (hm : m < 8) (hn : n < 8) :
    readTileC (physStep rf d) d.acc0 m n =
      readTileC rf d.acc0 m n + physSlab rf d m n := by
  unfold physStep
  exact readTileC_writeTileC rf d.acc0 _ m n hm hn

theorem physStep_frame (rf : RegFile) (d : FmhaDpas) (r e : Nat)
    (h : ¬ inTileC d.acc0 r e) : physStep rf d r e = rf r e := by
  unfold physStep
  exact writeTileC_frame rf d.acc0 _ r e h

/-- A C block does not disturb a physical A read that is entirely below it. -/
theorem readA16_writeTileC_below (rf : RegFile) (C : Nat → Nat → Word)
    (base acc m k : Nat) (hm : m < 8) (h : base + 8 ≤ acc) :
    readA16 (writeTileC rf acc C) base m k = readA16 rf base m k := by
  unfold readA16 writeTileC inTileC bf16Half
  have hnot : ¬ (acc ≤ base + m ∧ base + m < acc + 8 ∧ k / 2 < 8) := by omega
  simp [hnot]

/-- A C block does not disturb a physical A read that is entirely above it. -/
theorem readA16_writeTileC_above (rf : RegFile) (C : Nat → Nat → Word)
    (base acc m k : Nat) (hm : m < 8) (h : acc + 8 ≤ base) :
    readA16 (writeTileC rf acc C) base m k = readA16 rf base m k := by
  unfold readA16 writeTileC inTileC bf16Half
  have hnot : ¬ (acc ≤ base + m ∧ base + m < acc + 8 ∧ k / 2 < 8) := by omega
  simp [hnot]

/-- A C block does not disturb a physical B read that is entirely below it. -/
theorem readB16_writeTileC_below (rf : RegFile) (C : Nat → Nat → Word)
    (base acc k n : Nat) (hn : n < 8) (h : base + 8 ≤ acc) :
    readB16 (writeTileC rf acc C) base k n = readB16 rf base k n := by
  unfold readB16 writeTileC inTileC bf16Half
  have hnot : ¬ (acc ≤ base + n ∧ base + n < acc + 8 ∧ k / 2 < 8) := by omega
  simp [hnot]

/-- A C block does not disturb a physical B read that is entirely above it. -/
theorem readB16_writeTileC_above (rf : RegFile) (C : Nat → Nat → Word)
    (base acc k n : Nat) (hn : n < 8) (h : acc + 8 ≤ base) :
    readB16 (writeTileC rf acc C) base k n = readB16 rf base k n := by
  unfold readB16 writeTileC inTileC bf16Half
  have hnot : ¬ (acc ≤ base + n ∧ base + n < acc + 8 ∧ k / 2 < 8) := by omega
  simp [hnot]

/-- A 4-register load fills four physical A rows. -/
theorem readA16_writeWindow (rf : RegFile) (base : Nat) (e : Exec) (f : Nat → Word)
    (m k : Nat) (hm : m < 4) (hk : k < 16)
    (ha : e.elementActive (m * 8 + k / 2) = true) :
    readA16 (writeWindow rf ⟨base, 4⟩ e f) base m k =
      bf16Half (f (m * 8 + k / 2)) k := by
  have hk8 : k / 2 < 8 := by omega
  have hdiv : (m * 8 + k / 2) / 8 = m := by
    rw [Nat.add_comm, Nat.mul_comm m 8]
    rw [Nat.add_mul_div_left (k / 2) m (y := 8) (by decide : 0 < 8), Nat.div_eq_of_lt hk8]
    omega
  have hmod : (m * 8 + k / 2) % 8 = k / 2 := by
    rw [Nat.add_comm, Nat.mul_comm m 8]
    rw [Nat.add_mul_mod_self_left (k / 2) 8 m, Nat.mod_eq_of_lt hk8]
  have hi : m * 8 + k / 2 < (⟨base, 4⟩ : TlaWindow).lanes := by
    show m * 8 + k / 2 < 32
    omega
  have hidx := TlaWindow.index_lane (⟨base, 4⟩ : TlaWindow) (m * 8 + k / 2) hi
  have hreg : (⟨base, 4⟩ : TlaWindow).laneReg (m * 8 + k / 2) = base + m := by
    unfold TlaWindow.laneReg; rw [hdiv]
  have helm : (⟨base, 4⟩ : TlaWindow).laneElem (m * 8 + k / 2) = k / 2 := by
    unfold TlaWindow.laneElem; rw [hmod]
  rw [hreg, helm] at hidx
  unfold readA16 writeWindow
  simp [hidx, ha]

/-- A 16-register load fills eight physical B columns. -/
theorem readB16_writeWindow (rf : RegFile) (base : Nat) (e : Exec) (f : Nat → Word)
    (k n : Nat) (hn : n < 8) (hk : k < 16)
    (ha : e.elementActive (n * 8 + k / 2) = true) :
    readB16 (writeWindow rf ⟨base, 16⟩ e f) base k n =
      bf16Half (f (n * 8 + k / 2)) k := by
  have hk8 : k / 2 < 8 := by omega
  have hdiv : (n * 8 + k / 2) / 8 = n := by
    rw [Nat.add_comm, Nat.mul_comm n 8]
    rw [Nat.add_mul_div_left (k / 2) n (y := 8) (by decide : 0 < 8), Nat.div_eq_of_lt hk8]
    omega
  have hmod : (n * 8 + k / 2) % 8 = k / 2 := by
    rw [Nat.add_comm, Nat.mul_comm n 8]
    rw [Nat.add_mul_mod_self_left (k / 2) 8 n, Nat.mod_eq_of_lt hk8]
  have hi : n * 8 + k / 2 < (⟨base, 16⟩ : TlaWindow).lanes := by
    show n * 8 + k / 2 < 128
    omega
  have hidx := TlaWindow.index_lane (⟨base, 16⟩ : TlaWindow) (n * 8 + k / 2) hi
  have hreg : (⟨base, 16⟩ : TlaWindow).laneReg (n * 8 + k / 2) = base + n := by
    unfold TlaWindow.laneReg; rw [hdiv]
  have helm : (⟨base, 16⟩ : TlaWindow).laneElem (n * 8 + k / 2) = k / 2 := by
    unfold TlaWindow.laneElem; rw [hmod]
  rw [hreg, helm] at hidx
  unfold readB16 writeWindow
  simp [hidx, ha]

/-- Fold the physical atom step. -/
def physRun (steps : List FmhaDpas) (rf : RegFile) : RegFile :=
  steps.foldl physStep rf

/-- A fixed-accumulator chain in the physical layout is the initial block plus
the ordered physical slab sum. -/
theorem physRun_fixed_acc (steps : List FmhaDpas) (rf : RegFile) (acc : Nat)
    (hacc : ∀ d, d ∈ steps → d.acc0 = acc)
    (hA : ∀ d, d ∈ steps → acc + 8 ≤ d.srcA ∨ d.srcA + 8 ≤ acc)
    (hB : ∀ d, d ∈ steps → acc + 8 ≤ d.srcB ∨ d.srcB + 8 ≤ acc) :
    ∀ m n, m < 8 → n < 8 →
      readTileC (physRun steps rf) acc m n =
        readTileC rf acc m n +
          (steps.map (fun d => physSlab rf d m n)).sum := by
  induction steps generalizing rf with
  | nil => intro m n _ _; simp [physRun]
  | cons d ds ih =>
      intro m n hm hn
      simp only [physRun, List.foldl_cons]
      have hd : d.acc0 = acc := hacc d (by simp)
      have hstep : readTileC (physStep rf d) acc m n =
          readTileC rf acc m n + physSlab rf d m n := by
        simpa [hd] using physStep_acc0 rf d m n hm hn
      change readTileC (physRun ds (physStep rf d)) acc m n = _
      rw [ih (physStep rf d)
        (fun e he => hacc e (by simp [he]))
        (fun e he => hA e (by simp [he]))
        (fun e he => hB e (by simp [he])) m n hm hn]
      have hmap : ds.map (fun e => physSlab (physStep rf d) e m n) =
          ds.map (fun e => physSlab rf e m n) := by
        apply List.map_congr_left
        intro e he
        unfold physSlab
        exact dpasSlab_congr 16 _ _ _ _ m n
          (fun k _ => by
            rcases hA e (by simp [he]) with h | h
            · unfold physStep
              exact readA16_writeTileC_above rf _ e.srcA d.acc0 m k hm
                (by simpa [hd] using h)
            · unfold physStep
              exact readA16_writeTileC_below rf _ e.srcA d.acc0 m k hm
                (by simpa [hd] using h))
          (fun k _ => by
            rcases hB e (by simp [he]) with h | h
            · unfold physStep
              exact readB16_writeTileC_above rf _ e.srcB d.acc0 k n hn
                (by simpa [hd] using h)
            · unfold physStep
              exact readB16_writeTileC_below rf _ e.srcB d.acc0 k n hn
                (by simpa [hd] using h))
      rw [hmap, hstep]
      simp [List.sum_cons, BitVec.add_assoc]

/-- The Q-side A load at PC 1004 (`r10:4`). -/
def load1004 : TlaBlock2d :=
  ⟨"(W) load.ugm.d32x64t.a32", ⟨1, 0, true⟩, "r10:4", "ss[a0.2][r2:1-0x10000]"⟩

set_option maxRecDepth 1000000 in
theorem parseLoad1004 :
    (fmhaParsedAt 1004).bind parseTlaBlock2dInstr = some load1004 := by
  decide

/-- PC 1004 fills four physical A rows starting at `r10`. -/
theorem load1004_feeds_physA (st : TlaState) (mem : TlaMem) (bti : Nat → Word)
    (p : TlaState × TlaMem) (h : tlaBlock2dLoadW? st mem bti ⟨10, 4⟩ load1004 = some p)
    (a : TlaAddr) (hp : parseTlaAddr load1004.addr = some a)
    (m k : Nat) (hm : m < 4) (hk : k < 16)
    (ha : load1004.exec.elementActive (m * 8 + k / 2) = true) :
    readA16 p.1.regs 10 m k =
      bf16Half (mem.loadTile (a.effAddr st bti) (m * 8 + k / 2)) k := by
  unfold tlaBlock2dLoadW? at h
  rw [hp] at h
  simp only at h
  cases h
  exact readA16_writeWindow st.regs 10 load1004.exec
    (fun l => mem.loadTile (a.effAddr st bti) l) m k hm hk ha

/-- PC 1543 fills eight physical B columns starting at `r46`. -/
theorem load1543_feeds_physB (st : TlaState) (mem : TlaMem) (bti : Nat → Word)
    (p : TlaState × TlaMem) (h : tlaBlock2dLoadW? st mem bti ⟨46, 16⟩ load1543 = some p)
    (a : TlaAddr) (hp : parseTlaAddr load1543.addr = some a)
    (k n : Nat) (hn : n < 8) (hk : k < 16)
    (ha : load1543.exec.elementActive (n * 8 + k / 2) = true) :
    readB16 p.1.regs 46 k n =
      bf16Half (mem.loadTile (a.effAddr st bti) (n * 8 + k / 2)) k := by
  unfold tlaBlock2dLoadW? at h
  rw [hp] at h
  simp only at h
  cases h
  exact readB16_writeWindow st.regs 46 load1543.exec
    (fun l => mem.loadTile (a.effAddr st bti) l) k n hn hk ha

end IntelGpu
