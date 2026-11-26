-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.MaskExec
public import Intel.LoopBodyExec

@[expose] public section

/-!
# Mask-aware execution for the loop body's non-`mov` instructions

`stepWith` applies a mask only to `movMasked`; every other instruction runs on
all lanes. This module adds `stepMasked`, which executes `add`, `add3`, `load`,
`loadScaled`, `store` and `storeScaled` under their `Exec` control as
predication rather than branching: all lanes are considered at once, an
inactive destination lane keeps its old register value, and an inactive store
lane emits no memory write. Source operands and store addresses are read at
the hardware lane, while the destination footprint is the unit-stride region
written by `writeMaskedWith` at `Exec.laneIndex`.

At a full execution control (`size = 32`, `offset = 0`, `noMask = false`) every
``laneActive`` is true for `l < 32` and every ``laneIndex`` is `l`, so the
masked step reads and writes exactly what `stepWith` does on those lanes. The
frame laws record what changes when the control is smaller or offset, and the
last section transfers the real loop body's `C[id] = A[id] + B[id]` effect to
`stepMasked`.
-/

namespace IntelGpu

noncomputable section

/-- The unit-stride destination region at element zero, used for the load
instructions whose payload names a bare register number. -/
def laneDest (r : Nat) : Grf := ⟨r, 0, 0, 0, 1, 1⟩

/-- The hardware lane at operand index `i`. The `_NM` spelling ignores the
printed channel offset, matching `Exec.laneActive`. -/
def Exec.hwLane (e : Exec) (i : Nat) : Nat :=
  if e.noMask then i else e.offset + i

@[simp] theorem Exec.hwLane_noMask (e : Exec) (hnm : e.noMask = true) (i : Nat) :
    e.hwLane i = i := by
  simp [Exec.hwLane, hnm]

@[simp] theorem Exec.hwLane_not_noMask (e : Exec) (hnm : e.noMask = false) (i : Nat) :
    e.hwLane i = e.offset + i := by
  simp [Exec.hwLane, hnm]

/-- On an active lane, the operand index maps back to that hardware lane. -/
theorem Exec.hwLane_laneIndex (e : Exec) (l : Nat)
    (hactive : e.laneActive l = true) : e.hwLane (e.laneIndex l) = l := by
  by_cases hnm : e.noMask
  · simp [Exec.hwLane, Exec.laneIndex, hnm]
  · have hf : e.noMask = false := by simpa using hnm
    rw [Exec.hwLane_not_noMask e hf, Exec.offset_add_laneIndex e hf l hactive]

/-- A mask-aware step. The six non-`mov` vector and memory instructions consume
their `Exec`; all other instructions retain the `stepWith` semantics. -/
def stepMaskedWith (alias : Nat → Nat) (typeOf : Nat → Option RegType) :
    RealState → RInstr → RealState
  | s, .add e dst a b =>
      writeMaskedWith alias s dst e (fun i =>
        binOpWide (isWideOf typeOf dst.num) (fun x y => x + y) (fun x y => x + y)
          (readSrcWith alias s a (e.hwLane i))
          (readSrcWith alias s b (e.hwLane i)))
  | s, .add3 e dst a b c =>
      writeMaskedWith alias s dst e (fun i =>
        add3Wide (isWideOf typeOf dst.num) (readSrcWith alias s a (e.hwLane i))
          (readSrcWith alias s b (e.hwLane i))
          (readSrcWith alias s c (e.hwLane i)))
  | s, .load e dst _ addrReg =>
      writeMaskedWith alias s (laneDest dst) e (fun i =>
        zext (load32 s.mem (readRegWith alias s addrReg (e.hwLane i)).toNat))
  | s, .loadScaled e dst _ base idx =>
      writeMaskedWith alias s (laneDest dst) e (fun i =>
        zext (load32 s.mem
          (readScalarWith alias s base +
            ((readRegWith alias s idx (e.hwLane i)) <<< 2)).toNat))
  | s, .store e addrReg _ src =>
      { s with
        mem := storeVec s.mem e.size
          (fun i => readRegWith alias s addrReg (e.hwLane i))
          (fun i => low32 (readRegWith alias s src (e.hwLane i))) }
  | s, .storeScaled e base idx _ src =>
      { s with
        mem := storeVec s.mem e.size
          (fun i => readScalarWith alias s base +
            ((readRegWith alias s idx (e.hwLane i)) <<< 2))
          (fun i => low32 (readRegWith alias s src (e.hwLane i))) }
  | s, i => stepWith alias typeOf s i

/-- The loop vector add's mask-aware step. -/
def stepMasked : RealState → RInstr → RealState :=
  stepMaskedWith vaLoopAlias vaLoopRegType

/-- The mask-aware straight-line fold. -/
def runMasked (s : RealState) (is : List RInstr) : RealState :=
  runRealWith stepMasked s is

/-! ## Agreement with `stepWith` at a full execution control -/

/-- A full mask enables every lane below 32 and selects that lane's operand. -/
@[simp] theorem exec32_size : (32 : Exec).size = 32 := rfl

@[simp] theorem exec32_offset : (32 : Exec).offset = 0 := rfl

@[simp] theorem exec32_noMask : (32 : Exec).noMask = false := rfl

theorem full32_lane (l : Nat) (hl : l < 32) :
    (32 : Exec).laneActive l = true ∧ (32 : Exec).laneIndex l = l := by
  simp [Exec.laneActive, Exec.laneIndex, hl]

/-- Register agreement for a masked `add` at the full 32-lane control. The
destination region must start at element zero with unit stride, as the loop
body's `add` does. -/
theorem stepMaskedWith_add_reg_full (alias : Nat → Nat)
    (typeOf : Nat → Option RegType) (s : RealState) (dst a b : Grf) (l : Nat)
    (hdst : dst.hstride = 1) (hbase : dst.row * 8 + dst.col = 0) (hl : l < 32) :
    (stepMaskedWith alias typeOf s (.add 32 dst a b)).regs (alias dst.num) l =
      (stepWith alias typeOf s (.add 32 dst a b)).regs (alias dst.num) l := by
  simp [stepMaskedWith, stepWith, writeMaskedWith, writeVecWith, setReg,
    Exec.laneActive, Exec.hwLane, hdst, hbase, hl]

/-- Register agreement for a masked `add3` at the full 32-lane control. -/
theorem stepMaskedWith_add3_reg_full (alias : Nat → Nat)
    (typeOf : Nat → Option RegType) (s : RealState) (dst a b c : Grf) (l : Nat)
    (hdst : dst.hstride = 1) (hbase : dst.row * 8 + dst.col = 0) (hl : l < 32) :
    (stepMaskedWith alias typeOf s (.add3 32 dst a b c)).regs (alias dst.num) l =
      (stepWith alias typeOf s (.add3 32 dst a b c)).regs (alias dst.num) l := by
  simp [stepMaskedWith, stepWith, writeMaskedWith, writeVecWith, setReg,
    Exec.laneActive, Exec.hwLane, hdst, hbase, hl]

/-- Register agreement for a masked `load` at the full 32-lane control. -/
theorem stepMaskedWith_load_reg_full (alias : Nat → Nat)
    (typeOf : Nat → Option RegType) (s : RealState) (dst : Nat) (w : Width)
    (addrReg : Nat) (l : Nat) (hl : l < 32) :
    (stepMaskedWith alias typeOf s (.load 32 dst w addrReg)).regs (alias dst) l =
      (stepWith alias typeOf s (.load 32 dst w addrReg)).regs (alias dst) l := by
  simp [stepMaskedWith, stepWith, laneDest, writeMaskedWith, writeVecWith, setReg,
    Exec.laneActive, Exec.hwLane, hl]

/-- Register agreement for a masked `loadScaled` at the full 32-lane control. -/
theorem stepMaskedWith_loadScaled_reg_full (alias : Nat → Nat)
    (typeOf : Nat → Option RegType) (s : RealState) (dst : Nat) (w : Width)
    (base idx : Nat) (l : Nat) (hl : l < 32) :
    (stepMaskedWith alias typeOf s (.loadScaled 32 dst w base idx)).regs (alias dst) l =
      (stepWith alias typeOf s (.loadScaled 32 dst w base idx)).regs (alias dst) l := by
  simp [stepMaskedWith, stepWith, laneDest, writeMaskedWith, writeVecWith, setReg,
    Exec.laneActive, Exec.hwLane, hl]

/-- Whole-state agreement for a masked `store` at the full 32-lane control. -/
theorem stepMaskedWith_store_eq_full (alias : Nat → Nat)
    (typeOf : Nat → Option RegType) (s : RealState) (addrReg : Nat) (w : Width)
    (src : Nat) :
    stepMaskedWith alias typeOf s (.store 32 addrReg w src) =
      stepWith alias typeOf s (.store 32 addrReg w src) := by
  simp [stepMaskedWith, stepWith, Exec.hwLane]

/-- Whole-state agreement for a masked `storeScaled` at the full 32-lane control. -/
theorem stepMaskedWith_storeScaled_eq_full (alias : Nat → Nat)
    (typeOf : Nat → Option RegType) (s : RealState) (base idx : Nat) (w : Width)
    (src : Nat) :
    stepMaskedWith alias typeOf s (.storeScaled 32 base idx w src) =
      stepWith alias typeOf s (.storeScaled 32 base idx w src) := by
  simp [stepMaskedWith, stepWith, Exec.hwLane]

/-! The same agreements at the loop vector add's aliases and types. -/

theorem stepMasked_load_reg (s : RealState) (dst : Nat) (w : Width) (addrReg l : Nat)
    (halias : vaLoopAlias dst = dst) (hl : l < 32) :
    (stepMasked s (.load 32 dst w addrReg)).regs dst l =
      (stepVAL s (.load 32 dst w addrReg)).regs dst l := by
  simpa [stepMasked, stepVAL, halias] using
    stepMaskedWith_load_reg_full vaLoopAlias vaLoopRegType s dst w addrReg l hl

theorem stepMasked_loadScaled_reg (s : RealState) (dst : Nat) (w : Width)
    (base idx l : Nat) (halias : vaLoopAlias dst = dst) (hl : l < 32) :
    (stepMasked s (.loadScaled 32 dst w base idx)).regs dst l =
      (stepVAL s (.loadScaled 32 dst w base idx)).regs dst l := by
  simpa [stepMasked, stepVAL, halias] using
    stepMaskedWith_loadScaled_reg_full vaLoopAlias vaLoopRegType s dst w base idx l hl

theorem stepMasked_add_reg (s : RealState) (dst a b : Grf) (l : Nat)
    (halias : vaLoopAlias dst.num = dst.num) (hdst : dst.hstride = 1)
    (hbase : dst.row * 8 + dst.col = 0) (hl : l < 32) :
    (stepMasked s (.add 32 dst a b)).regs dst.num l =
      (stepVAL s (.add 32 dst a b)).regs dst.num l := by
  simpa [stepMasked, stepVAL, halias] using
    stepMaskedWith_add_reg_full vaLoopAlias vaLoopRegType s dst a b l hdst hbase hl

theorem stepMasked_add3_reg (s : RealState) (dst a b c : Grf) (l : Nat)
    (halias : vaLoopAlias dst.num = dst.num) (hdst : dst.hstride = 1)
    (hbase : dst.row * 8 + dst.col = 0) (hl : l < 32) :
    (stepMasked s (.add3 32 dst a b c)).regs dst.num l =
      (stepVAL s (.add3 32 dst a b c)).regs dst.num l := by
  simpa [stepMasked, stepVAL, halias] using
    stepMaskedWith_add3_reg_full vaLoopAlias vaLoopRegType s dst a b c l hdst hbase hl

theorem stepMasked_store_eq (s : RealState) (addrReg : Nat) (w : Width) (src : Nat) :
    stepMasked s (.store 32 addrReg w src) = stepVAL s (.store 32 addrReg w src) := by
  simpa [stepMasked, stepVAL] using
    stepMaskedWith_store_eq_full vaLoopAlias vaLoopRegType s addrReg w src

theorem stepMasked_storeScaled_eq (s : RealState) (base idx : Nat) (w : Width)
    (src : Nat) :
    stepMasked s (.storeScaled 32 base idx w src) =
      stepVAL s (.storeScaled 32 base idx w src) := by
  simpa [stepMasked, stepVAL] using
    stepMaskedWith_storeScaled_eq_full vaLoopAlias vaLoopRegType s base idx w src

/-! ## Frame laws -/

/-- Operand index `i` names an active hardware lane whenever `i < size`. -/
theorem Exec.laneActive_hwLane (e : Exec) (i : Nat) (hi : i < e.size) :
    e.laneActive (e.hwLane i) = true := by
  by_cases hnm : e.noMask
  · simp [Exec.hwLane, Exec.laneActive, hnm, hi]
  · have hf : e.noMask = false := by simpa using hnm
    simp [Exec.hwLane, Exec.laneActive, hf, hi]

/-- A masked `add` leaves every destination element that no active lane writes
at its prior value. -/
theorem stepMaskedWith_add_frame (alias : Nat → Nat)
    (typeOf : Nat → Option RegType) (s : RealState) (e : Exec) (dst a b : Grf)
    (j : Nat) (hdst : dst.hstride = 1)
    (hframe : ∀ l, e.laneActive l = true → j ≠ dst.dstIndex (e.laneIndex l)) :
    (stepMaskedWith alias typeOf s (.add e dst a b)).regs (alias dst.num) j =
      s.regs (alias dst.num) j := by
  simpa [stepMaskedWith] using
    writeMaskedWith_unit_frame alias s dst e _ hdst j hframe

/-- A masked `add3` leaves every destination element that no active lane
writes at its prior value. -/
theorem stepMaskedWith_add3_frame (alias : Nat → Nat)
    (typeOf : Nat → Option RegType) (s : RealState) (e : Exec) (dst a b c : Grf)
    (j : Nat) (hdst : dst.hstride = 1)
    (hframe : ∀ l, e.laneActive l = true → j ≠ dst.dstIndex (e.laneIndex l)) :
    (stepMaskedWith alias typeOf s (.add3 e dst a b c)).regs (alias dst.num) j =
      s.regs (alias dst.num) j := by
  simpa [stepMaskedWith] using
    writeMaskedWith_unit_frame alias s dst e _ hdst j hframe

/-- A masked `load` leaves every destination element outside the active
operand indices at its prior value. -/
theorem stepMaskedWith_load_frame (alias : Nat → Nat)
    (typeOf : Nat → Option RegType) (s : RealState) (e : Exec) (dst : Nat)
    (w : Width) (addrReg j : Nat)
    (hframe : ∀ l, e.laneActive l = true → j ≠ e.laneIndex l) :
    (stepMaskedWith alias typeOf s (.load e dst w addrReg)).regs (alias dst) j =
      s.regs (alias dst) j := by
  simpa [stepMaskedWith, laneDest, Grf.dstIndex] using
    writeMaskedWith_unit_frame alias s (laneDest dst) e _ rfl j (by
      intro l hactive
      simpa [laneDest, Grf.dstIndex] using hframe l hactive)

/-- A masked `loadScaled` leaves every destination element outside the active
operand indices at its prior value. -/
theorem stepMaskedWith_loadScaled_frame (alias : Nat → Nat)
    (typeOf : Nat → Option RegType) (s : RealState) (e : Exec) (dst : Nat)
    (w : Width) (base idx j : Nat)
    (hframe : ∀ l, e.laneActive l = true → j ≠ e.laneIndex l) :
    (stepMaskedWith alias typeOf s (.loadScaled e dst w base idx)).regs
        (alias dst) j = s.regs (alias dst) j := by
  simpa [stepMaskedWith, laneDest, Grf.dstIndex] using
    writeMaskedWith_unit_frame alias s (laneDest dst) e _ rfl j (by
      intro l hactive
      simpa [laneDest, Grf.dstIndex] using hframe l hactive)

/-- A masked `add` leaves destination element `j` at its prior value when `j`
lies at or beyond the execution size. This covers both a smaller control and a
nonzero channel offset, since active operand indices are always below `size`. -/
theorem stepMaskedWith_add_uncovered (alias : Nat → Nat)
    (typeOf : Nat → Option RegType) (s : RealState) (e : Exec) (dst a b : Grf)
    (j : Nat) (hdst : dst.hstride = 1) (hbase : dst.row * 8 + dst.col = 0)
    (hj : e.size ≤ j) :
    (stepMaskedWith alias typeOf s (.add e dst a b)).regs (alias dst.num) j =
      s.regs (alias dst.num) j := by
  refine stepMaskedWith_add_frame alias typeOf s e dst a b j hdst ?_
  intro l hactive hEq
  have hlt := Exec.laneIndex_lt_size e l hactive
  have hji : j = e.laneIndex l := by
    simpa [Grf.dstIndex, hdst, hbase] using hEq
  omega

/-- A masked `add3` leaves destination element `j` at its prior value when `j`
lies at or beyond the execution size. -/
theorem stepMaskedWith_add3_uncovered (alias : Nat → Nat)
    (typeOf : Nat → Option RegType) (s : RealState) (e : Exec) (dst a b c : Grf)
    (j : Nat) (hdst : dst.hstride = 1) (hbase : dst.row * 8 + dst.col = 0)
    (hj : e.size ≤ j) :
    (stepMaskedWith alias typeOf s (.add3 e dst a b c)).regs (alias dst.num) j =
      s.regs (alias dst.num) j := by
  refine stepMaskedWith_add3_frame alias typeOf s e dst a b c j hdst ?_
  intro l hactive hEq
  have hlt := Exec.laneIndex_lt_size e l hactive
  have hji : j = e.laneIndex l := by
    simpa [Grf.dstIndex, hdst, hbase] using hEq
  omega

/-- A masked `load` leaves destination element `j` at its prior value when `j`
lies at or beyond the execution size. -/
theorem stepMaskedWith_load_uncovered (alias : Nat → Nat)
    (typeOf : Nat → Option RegType) (s : RealState) (e : Exec) (dst : Nat)
    (w : Width) (addrReg j : Nat) (hj : e.size ≤ j) :
    (stepMaskedWith alias typeOf s (.load e dst w addrReg)).regs (alias dst) j =
      s.regs (alias dst) j := by
  refine stepMaskedWith_load_frame alias typeOf s e dst w addrReg j ?_
  intro l hactive hEq
  have hlt := Exec.laneIndex_lt_size e l hactive
  omega

/-- A masked `loadScaled` leaves destination element `j` at its prior value when
`j` lies at or beyond the execution size. -/
theorem stepMaskedWith_loadScaled_uncovered (alias : Nat → Nat)
    (typeOf : Nat → Option RegType) (s : RealState) (e : Exec) (dst : Nat)
    (w : Width) (base idx j : Nat) (hj : e.size ≤ j) :
    (stepMaskedWith alias typeOf s (.loadScaled e dst w base idx)).regs
        (alias dst) j = s.regs (alias dst) j := by
  refine stepMaskedWith_loadScaled_frame alias typeOf s e dst w base idx j ?_
  intro l hactive hEq
  have hlt := Exec.laneIndex_lt_size e l hactive
  omega

/-- A masked store leaves a word unchanged when no stored lane address maps to
it. The hypothesis is on the executed operand indices `i < size`. -/
theorem stepMaskedWith_store_frame (alias : Nat → Nat)
    (typeOf : Nat → Option RegType) (s : RealState) (e : Exec) (addrReg : Nat)
    (w : Width) (src : Nat) (target : Nat)
    (hframe : ∀ i, i < e.size →
      (readRegWith alias s addrReg (e.hwLane i)).toNat / 4 ≠ target) :
    (stepMaskedWith alias typeOf s (.store e addrReg w src)).mem target =
      s.mem target := by
  simpa [stepMaskedWith] using
    storeVec_frame s.mem e.size
      (fun i => readRegWith alias s addrReg (e.hwLane i))
      (fun i => low32 (readRegWith alias s src (e.hwLane i))) target hframe

/-- A masked scaled store leaves a word unchanged when no stored lane address
maps to it. -/
theorem stepMaskedWith_storeScaled_frame (alias : Nat → Nat)
    (typeOf : Nat → Option RegType) (s : RealState) (e : Exec) (base idx : Nat)
    (w : Width) (src : Nat) (target : Nat)
    (hframe : ∀ i, i < e.size →
      (readScalarWith alias s base +
        ((readRegWith alias s idx (e.hwLane i)) <<< 2)).toNat / 4 ≠ target) :
    (stepMaskedWith alias typeOf s (.storeScaled e base idx w src)).mem target =
      s.mem target := by
  simpa [stepMaskedWith] using
    storeVec_frame s.mem e.size
      (fun i => readScalarWith alias s base +
        ((readRegWith alias s idx (e.hwLane i)) <<< 2))
      (fun i => low32 (readRegWith alias s src (e.hwLane i))) target hframe

/-- An inactive hardware lane writes no memory at its own address, provided no
active lane's store aliases that address. -/
theorem stepMaskedWith_store_inactive (alias : Nat → Nat)
    (typeOf : Nat → Option RegType) (s : RealState) (e : Exec) (addrReg : Nat)
    (w : Width) (src l : Nat) (_hinactive : e.laneActive l = false)
    (hdistinct : ∀ k, e.laneActive k = true →
      (readRegWith alias s addrReg k).toNat / 4 ≠
        (readRegWith alias s addrReg l).toNat / 4) :
    (stepMaskedWith alias typeOf s (.store e addrReg w src)).mem
        ((readRegWith alias s addrReg l).toNat / 4) =
      s.mem ((readRegWith alias s addrReg l).toNat / 4) := by
  refine stepMaskedWith_store_frame alias typeOf s e addrReg w src _ ?_
  intro i hi
  exact hdistinct (e.hwLane i) (Exec.laneActive_hwLane e i hi)

/-- An inactive hardware lane writes no memory at its own scaled address,
provided no active lane's store aliases that address. -/
theorem stepMaskedWith_storeScaled_inactive (alias : Nat → Nat)
    (typeOf : Nat → Option RegType) (s : RealState) (e : Exec) (base idx : Nat)
    (w : Width) (src l : Nat) (_hinactive : e.laneActive l = false)
    (hdistinct : ∀ k, e.laneActive k = true →
      (readScalarWith alias s base +
        ((readRegWith alias s idx k) <<< 2)).toNat / 4 ≠
      (readScalarWith alias s base +
        ((readRegWith alias s idx l) <<< 2)).toNat / 4) :
    (stepMaskedWith alias typeOf s (.storeScaled e base idx w src)).mem
        ((readScalarWith alias s base +
          ((readRegWith alias s idx l) <<< 2)).toNat / 4) =
      s.mem ((readScalarWith alias s base +
        ((readRegWith alias s idx l) <<< 2)).toNat / 4) := by
  refine stepMaskedWith_storeScaled_frame alias typeOf s e base idx w src _ ?_
  intro i hi
  exact hdistinct (e.hwLane i) (Exec.laneActive_hwLane e i hi)

/-- A masked store does not change registers. -/
theorem stepMasked_store_regs (s : RealState) (addrReg : Nat) (w : Width) (src r j : Nat) :
    (stepMasked s (.store 32 addrReg w src)).regs r j = s.regs r j := by
  simp [stepMasked, stepMaskedWith]

/-- A masked scaled store does not change registers. -/
theorem stepMasked_storeScaled_regs (s : RealState) (base idx : Nat) (w : Width)
    (src r j : Nat) :
    (stepMasked s (.storeScaled 32 base idx w src)).regs r j = s.regs r j := by
  simp [stepMasked, stepMaskedWith]

/-- The uniform scaled store does not change registers. -/
theorem stepVAL_storeScaled_regs (s : RealState) (base idx : Nat) (w : Width)
    (src r j : Nat) :
    (stepVAL s (.storeScaled 32 base idx w src)).regs r j = s.regs r j := by
  simp [stepVAL, stepWith]

/-- The uniform store does not change registers. -/
theorem stepVAL_store_regs (s : RealState) (addrReg : Nat) (w : Width) (src r j : Nat) :
    (stepVAL s (.store 32 addrReg w src)).regs r j = s.regs r j := by
  simp [stepVAL, stepWith]

/-! ## Agreement below the execution window -/

/-- Two states agree on every register lane below `n` and on all of memory. -/
def AgreesBelow (n : Nat) (s1 s2 : RealState) : Prop :=
  (∀ r l, l < n → s1.regs r l = s2.regs r l) ∧ s1.mem = s2.mem

theorem agreesBelow_refl (n : Nat) (s : RealState) : AgreesBelow n s s :=
  ⟨fun _ _ _ => rfl, rfl⟩

/-- A full-control masked `loadScaled` preserves lane agreement with `stepVAL`. -/
theorem agreesBelow_loadScaled {s1 s2 : RealState} (h : AgreesBelow 32 s1 s2)
    (dst : Nat) (w : Width) (base idx : Nat) :
    AgreesBelow 32 (stepMasked s1 (.loadScaled 32 dst w base idx))
      (stepVAL s2 (.loadScaled 32 dst w base idx)) := by
  constructor
  · intro r l hl
    by_cases hr : r = vaLoopAlias dst
    · subst r
      simp [stepMasked, stepMaskedWith, stepVAL, stepWith, laneDest, writeMaskedWith,
        writeVecWith, setReg, readScalarWith, readRegWith, Exec.laneActive,
        Exec.hwLane, hl, h.1 (vaLoopAlias base) 0 (by omega),
        h.1 (vaLoopAlias idx) l hl, h.2]
    · simp [stepMasked, stepMaskedWith, stepVAL, stepWith, laneDest, writeMaskedWith,
        writeVecWith, setReg, hr, h.1 r l hl]
  · simp [stepMasked, stepMaskedWith, stepVAL, stepWith, laneDest,
      writeMaskedWith, writeVecWith, h.2]

/-- A full-control masked `add` preserves lane agreement with `stepVAL`, when
both source regions stay below lane 32. -/
theorem agreesBelow_add {s1 s2 : RealState} (h : AgreesBelow 32 s1 s2)
    (dst a b : Grf) (hdst : dst.hstride = 1) (hbase : dst.row * 8 + dst.col = 0)
    (ha : ∀ l, l < 32 → srcIndex a l < 32)
    (hb : ∀ l, l < 32 → srcIndex b l < 32) :
    AgreesBelow 32 (stepMasked s1 (.add 32 dst a b))
      (stepVAL s2 (.add 32 dst a b)) := by
  constructor
  · intro r l hl
    by_cases hr : r = vaLoopAlias dst.num
    · subst r
      have hsa : s1.regs (vaLoopAlias a.num)
          (a.row * 8 + a.col + if a.vstride = 0 then 0 else l) =
          s2.regs (vaLoopAlias a.num)
            (a.row * 8 + a.col + if a.vstride = 0 then 0 else l) :=
        h.1 _ _ (by simpa [srcIndex] using ha l hl)
      have hsb : s1.regs (vaLoopAlias b.num)
          (b.row * 8 + b.col + if b.vstride = 0 then 0 else l) =
          s2.regs (vaLoopAlias b.num)
            (b.row * 8 + b.col + if b.vstride = 0 then 0 else l) :=
        h.1 _ _ (by simpa [srcIndex] using hb l hl)
      simp [stepMasked, stepMaskedWith, stepVAL, stepWith, writeMaskedWith,
        writeVecWith, setReg, readSrcWith, srcIndex, readRegWith, Exec.laneActive,
        Exec.hwLane, hdst, hbase, hl, hsa, hsb]
    · simp [stepMasked, stepMaskedWith, stepVAL, stepWith, writeMaskedWith,
        writeVecWith, setReg, hr, h.1 r l hl]
  · simp [stepMasked, stepMaskedWith, stepVAL, stepWith, writeMaskedWith,
      writeVecWith, h.2]

/-! ## The real loop body -/

/-- The three body instructions before the store preserve agreement below
lane 32. -/
theorem vaLoopBody_preStore_agreesBelow (s : RealState) :
    AgreesBelow 32
      (stepMasked
        (stepMasked (stepMasked s (.loadScaled 32 69 .d32 47 59))
          (.loadScaled 32 70 .d32 48 59))
        (.add 32 ⟨71, 0, 0, 1, 1, 1⟩ ⟨69, 0, 0, 1, 1, 0⟩
          ⟨70, 0, 0, 1, 1, 0⟩))
      (stepVAL
        (stepVAL (stepVAL s (.loadScaled 32 69 .d32 47 59))
          (.loadScaled 32 70 .d32 48 59))
        (.add 32 ⟨71, 0, 0, 1, 1, 1⟩ ⟨69, 0, 0, 1, 1, 0⟩
          ⟨70, 0, 0, 1, 1, 0⟩)) := by
  have h1 := agreesBelow_loadScaled (agreesBelow_refl 32 s) 69 .d32 47 59
  have h2 := agreesBelow_loadScaled h1 70 .d32 48 59
  exact agreesBelow_add h2 ⟨71, 0, 0, 1, 1, 1⟩ ⟨69, 0, 0, 1, 1, 0⟩
    ⟨70, 0, 0, 1, 1, 0⟩ (by decide) (by decide)
    (fun l hl => by simpa [srcIndex] using hl)
    (fun l hl => by simpa [srcIndex] using hl)

/-- At `l < 32`, masked execution of the four-instruction loop body leaves
registers 69, 70 and 71 exactly as the uniform `stepVAL` run does. -/
theorem vaLoopBody_runMasked_regs (s : RealState) (l : Nat) (hl : l < 32) :
    (runMasked s vaLoopBody).regs 69 l = (runVAL s vaLoopBody).regs 69 l ∧
    (runMasked s vaLoopBody).regs 70 l = (runVAL s vaLoopBody).regs 70 l ∧
    (runMasked s vaLoopBody).regs 71 l = (runVAL s vaLoopBody).regs 71 l := by
  have h := vaLoopBody_preStore_agreesBelow s
  unfold runMasked runVAL vaLoopBody
  simp only [runRealWith, List.foldl_cons, List.foldl_nil]
  rw [stepMasked_storeScaled_eq]
  refine ⟨?_, ?_, ?_⟩
  · simpa [stepVAL_storeScaled_regs] using h.1 69 l hl
  · simpa [stepVAL_storeScaled_regs] using h.1 70 l hl
  · simpa [stepVAL_storeScaled_regs] using h.1 71 l hl

/-- The masked body's memory is a store of the lane sums at the C addresses. -/
theorem vaLoopBody_runMasked_mem_at (s : RealState) (aPtr bPtr cPtr : Addr)
    (idx : Nat → Addr) (h : VaLoopBodyPre s aPtr bPtr cPtr idx) :
    (runMasked s vaLoopBody).mem =
      storeVec s.mem 32
        (fun l => cPtr + (idx l) <<< 2)
        (fun l => low32 ((runMasked s vaLoopBody).regs 71 l)) := by
  unfold runMasked vaLoopBody
  simp [runRealWith, stepMasked, stepMaskedWith, laneDest, writeMaskedWith,
    Exec.hwLane, Exec.laneActive, vaLoopAlias, readScalarWith, readRegWith,
    h.aReg, h.bReg, h.cReg, h.idxReg]

/-- Masked execution of the body stores each lane's sum at C[index]. -/
theorem vaLoopBody_runMasked_store_at (s : RealState) (aPtr bPtr cPtr : Addr)
    (idx : Nat → Addr) (h : VaLoopBodyPre s aPtr bPtr cPtr idx) (l : Nat)
    (hl : l < 32) (ha : aPtr.toNat % 4 = 0) (hb : bPtr.toNat % 4 = 0)
    (hc : cPtr.toNat % 4 = 0)
    (hab : aPtr.toNat + 4 * (idx l).toNat < 2 ^ 64)
    (hbb : bPtr.toNat + 4 * (idx l).toNat < 2 ^ 64)
    (hcb : cPtr.toNat + 4 * (idx l).toNat < 2 ^ 64)
    (hboundC : ∀ k, k < 32 → cPtr.toNat + 4 * (idx k).toNat < 2 ^ 64)
    (hdistinct : ∀ k, k < 32 → k ≠ l → cPtr.toNat / 4 + (idx k).toNat ≠
      cPtr.toNat / 4 + (idx l).toNat) :
    (runMasked s vaLoopBody).mem (cPtr.toNat / 4 + (idx l).toNat) =
      s.mem (aPtr.toNat / 4 + (idx l).toNat) +
        s.mem (bPtr.toNat / 4 + (idx l).toNat) := by
  rw [vaLoopBody_runMasked_mem_at s aPtr bPtr cPtr idx h]
  have hdistinct' : ∀ k, k < 32 → k ≠ l →
      (cPtr + (idx k) <<< 2).toNat / 4 ≠ (cPtr + (idx l) <<< 2).toNat / 4 := by
    intro k hk hne
    rw [vaLoopWordBitVec cPtr (idx k) hc (hboundC k hk),
      vaLoopWordBitVec cPtr (idx l) hc hcb]
    exact hdistinct k hk hne
  have hsame := storeVec_same s.mem 32 (fun l' => cPtr + (idx l') <<< 2)
    (fun l' => low32 ((runMasked s vaLoopBody).regs 71 l')) l hl hdistinct'
  rw [vaLoopWordBitVec cPtr (idx l) hc hcb] at hsame
  rw [hsame]
  have h71 := (vaLoopBody_runMasked_regs s l hl).2.2
  rw [h71]
  exact vaLoopBody_sum s aPtr bPtr cPtr idx h l ha hb hab hbb


/-! ## Negative controls -/

/-- A 16-lane masked add leaves destination element 20 at its prior value. -/
theorem maskedAdd_smaller_uncovered (alias : Nat → Nat)
    (typeOf : Nat → Option RegType) (s : RealState) (dst a b : Grf)
    (hdst : dst.hstride = 1) (hbase : dst.row * 8 + dst.col = 0) :
    (stepMaskedWith alias typeOf s (.add ⟨16, 0, false⟩ dst a b)).regs
        (alias dst.num) 20 = s.regs (alias dst.num) 20 := by
  refine stepMaskedWith_add_uncovered alias typeOf s ⟨16, 0, false⟩ dst a b 20
    hdst hbase ?_
  decide

/-- A 16-lane masked load with channel offset 16 leaves destination element 16
at its prior value; the active hardware lanes map to operand indices 0--15. -/
theorem maskedLoad_offset_uncovered (alias : Nat → Nat)
    (typeOf : Nat → Option RegType) (s : RealState) (dst : Nat) (w : Width)
    (addrReg : Nat) :
    (stepMaskedWith alias typeOf s (.load ⟨16, 16, false⟩ dst w addrReg)).regs
        (alias dst) 16 = s.regs (alias dst) 16 := by
  refine stepMaskedWith_load_uncovered alias typeOf s ⟨16, 16, false⟩ dst w
    addrReg 16 ?_
  decide

/-- The offset is consumed: hardware lane 16 writes destination element 0. -/
theorem maskedLoad_offset_covers (alias : Nat → Nat)
    (typeOf : Nat → Option RegType) (s : RealState) (dst : Nat) (w : Width)
    (addrReg : Nat) :
    (stepMaskedWith alias typeOf s (.load ⟨16, 16, false⟩ dst w addrReg)).regs
        (alias dst) 0 =
      zext (load32 s.mem (readRegWith alias s addrReg 16).toNat) := by
  simp [stepMaskedWith, laneDest, writeMaskedWith, Exec.hwLane, Exec.laneActive]

end

end IntelGpu
