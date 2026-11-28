-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.LoopMemoryTransport
public import Intel.LoopPackIncBoth
public import Intel.GridStride

@[expose] public section

/-!
# The decoded loop-back block and the grid-stride step

The decoded loop vector add has a loop-back block at PCs 36--43:

```
36  _0_010:
37  sel (P6) V0079 <- V0075 / V0062
38  sel (P6) V0080 <- V0076 / V0063
39  mov  (16|M0)  V0081(0,0)<2>  V0082(0,0)<1;1,0>
40  mov  (16|M16) V0081(2,0)<2>  V0082(1,0)<1;1,0>
41  mov  (16|M0)  V0081(0,1)<2>  V0083(0,0)<1;1,0>
42  mov  (16|M16) V0081(2,1)<2>  V0083(1,0)<1;1,0>
43  goto 1 _0_009
```

`V0081`, `V0082` and `V0083` alias `V0059`, `V0079` and `V0080`, and
`_0_009` is PC 20. Thus the block is exactly the loop's grid-stride update:
it selects the incremented ID on lanes whose continuation predicate `P6` is
true and writes the 24-lane dword pack back into `V0059`. The first
iteration's exit path (PC 17 to PC 44) is stage 136
(`vaLoop_lane_body_exit`); this module supplies the loop-back edge that stage
136 deliberately left out.

The value-level statement is `vaLoop_loopBack_id`: at PC 36, for `l < 24`,
the qword view of `V0059` after the block is

```
selectId old (fun k => old k + stride) (fun k => s.preds 6 k) l
```

where `old = fun k => s.regs 59 k` and `stride` is the work-group size read
into `V0067`. The pre-state facts are bundled in `VaLoopLoopBackPre`: the low
and high dwords of `V0062/V0063` hold the old ID and those of `V0075/V0076`
hold `old + stride` (the `V0072` increment followed by the PC 26--29 packs).

`RealState` stores one 64-bit slot per element, so the four final moves write
the 24-lane dword pack into dword slots 0..47; `dwordReg` and `qwordOf`
reconstruct the qword-per-lane `V0059` value. This is the same dword/qword
bridge as `Intel.DwordView` and `Intel.LoopPack`; the raw `regs 59 l` slot for
`l < 24` is a dword slot, not the qword lane. The exact l >= 24 frame is for
the qword view, and `vaLoopLoopBack_dword_counterexample` shows that the naive
all-32-lane `regs 59 l` claim is false.

The second-body theorem `vaLoop_lane_second_body` composes the decoded control
edge PC 35 -> 36 -> ... -> 20 -> 21 with a value-level re-entry state whose
`V0059` lanes are the selected IDs. It then applies the existing body store
lemma to the updated index `old l + stride`. The literal interpreter would
still read the dword slots of `V0059` at PC 21; coalescing those slots back
into qword lanes is the model boundary documented at the end of this file.

Everything here uses the per-lane interpreter, `stepLoop`, and the decoded
program `vaLoopProgram`.
-/

namespace IntelGpu

noncomputable section

/-! ## The decoded PC 36--43 block -/

/-- Destination of the first low-dword move at PC 39. -/
def dst81Even : Grf := ⟨81, 0, 0, 1, 1, 2⟩
/-- Destination of the second low-dword move at PC 40. -/
def dst81EvenM5 : Grf := ⟨81, 2, 0, 1, 1, 2⟩
/-- Destination of the first high-dword move at PC 41. -/
def dst81Odd : Grf := ⟨81, 0, 1, 1, 1, 2⟩
/-- Destination of the second high-dword move at PC 42. -/
def dst81OddM5 : Grf := ⟨81, 2, 1, 1, 1, 2⟩
/-- First low-dword source, alias `V0082 = V0079`. -/
def src79Even : Grf := ⟨82, 0, 0, 1, 1, 0⟩
/-- Second low-dword source, alias `V0082 = V0079`. -/
def src79EvenM5 : Grf := ⟨82, 1, 0, 1, 1, 0⟩
/-- First high-dword source, alias `V0083 = V0080`. -/
def src80Odd : Grf := ⟨83, 0, 0, 1, 1, 0⟩
/-- Second high-dword source, alias `V0083 = V0080`. -/
def src80OddM5 : Grf := ⟨83, 1, 0, 1, 1, 0⟩

/-- PC 37: select the old/new low dwords by `P6`. -/
def vaLoopSelLow : RInstr := .sel 32 6 ⟨79, 0, 0, 1, 1, 1⟩
  ⟨75, 0, 0, 1, 1, 0⟩ ⟨62, 0, 0, 1, 1, 0⟩
/-- PC 38: select the old/new high dwords by `P6`. -/
def vaLoopSelHigh : RInstr := .sel 32 6 ⟨80, 0, 0, 1, 1, 1⟩
  ⟨76, 0, 0, 1, 1, 0⟩ ⟨63, 0, 0, 1, 1, 0⟩
/-- PC 39: first low-dword pack move. -/
def vaLoopMovLowA : RInstr := .mov e1Loop dst81Even src79Even
/-- PC 40: second low-dword pack move. -/
def vaLoopMovLowB : RInstr := .movMasked e2Loop dst81EvenM5 src79EvenM5
/-- PC 41: first high-dword pack move. -/
def vaLoopMovHighA : RInstr := .mov e1Loop dst81Odd src80Odd
/-- PC 42: second high-dword pack move. -/
def vaLoopMovHighB : RInstr := .movMasked e2Loop dst81OddM5 src80OddM5

/-- The two low-dword pack moves. -/
def vaLoopLowPack : List RInstr := [vaLoopMovLowA, vaLoopMovLowB]
/-- The two high-dword pack moves. -/
def vaLoopHighPack : List RInstr := [vaLoopMovHighA, vaLoopMovHighB]
/-- The four writeback moves at PCs 39--42. -/
def vaLoopWriteBackSlice : List RInstr := vaLoopLowPack ++ vaLoopHighPack
/-- The six state-changing instructions at PCs 37--42. -/
def vaLoopLoopBackSlice : List RInstr :=
  [vaLoopSelLow, vaLoopSelHigh] ++ vaLoopWriteBackSlice

theorem vaLoopProgram_36 :
    vaLoopProgram[36]? = some (.label "_0_010") := by decide
theorem vaLoopProgram_37 : vaLoopProgram[37]? = some vaLoopSelLow := by decide
theorem vaLoopProgram_38 : vaLoopProgram[38]? = some vaLoopSelHigh := by decide
theorem vaLoopProgram_39 : vaLoopProgram[39]? = some vaLoopMovLowA := by decide
theorem vaLoopProgram_40 : vaLoopProgram[40]? = some vaLoopMovLowB := by decide
theorem vaLoopProgram_41 : vaLoopProgram[41]? = some vaLoopMovHighA := by decide
theorem vaLoopProgram_42 : vaLoopProgram[42]? = some vaLoopMovHighB := by decide
theorem vaLoopProgram_43 :
    vaLoopProgram[43]? = some (.goto 1 "_0_009") := by decide

theorem vaLoopLoopBackSlice_eq :
    (vaLoopProgram.drop 37).take 6 = vaLoopLoopBackSlice := by decide

/-! ## Instruction-level value laws -/

/-- A stride-two `_NM`/masked destination move writes the active lane's source
element at `base + 2 * (lane - maskOffset)`. -/
theorem stepLoop_mov_stride2_value (s : RealState) (e : Exec) (dst src : Grf)
    (h61 : src.num ≠ 61) (h74 : src.num ≠ 74)
    (hnm : e.noMask = false) (hdst : dst.hstride = 2)
    (l : Nat) (hactive : e.laneActive l = true) :
    (stepLoop s (.mov e dst src)).regs (vaLoopAlias dst.num)
        (dst.dstIndex (e.laneIndex l)) =
      readSrcWith vaLoopAlias s src (e.laneIndex l) := by
  have hle : e.offset ≤ l := by
    have h := hactive
    simp [Exec.laneActive, hnm] at h
    exact h.1
  have hmod : (l - e.offset) * 2 % 2 = 0 := by
    rw [Nat.mul_comm]
    exact Nat.mul_mod_right 2 (l - e.offset)
  have hdiv : (l - e.offset) * 2 / 2 = l - e.offset := by
    rw [Nat.mul_comm]
    exact Nat.mul_div_right (l - e.offset) (by decide : 0 < 2)
  simp [stepLoop, h61, h74, writeMaskedWith, Grf.dstIndex, Exec.laneIndex, hnm,
    hdst, Nat.add_sub_of_le hle, hactive, hmod, hdiv]

/-- The same stride-two law for an explicitly masked move. -/
theorem stepLoop_movMasked_stride2_value (s : RealState) (e : Exec) (dst src : Grf)
    (h61 : src.num ≠ 61) (h74 : src.num ≠ 74)
    (hnm : e.noMask = false) (hdst : dst.hstride = 2)
    (l : Nat) (hactive : e.laneActive l = true) :
    (stepLoop s (.movMasked e dst src)).regs (vaLoopAlias dst.num)
        (dst.dstIndex (e.laneIndex l)) =
      readSrcWith vaLoopAlias s src (e.laneIndex l) := by
  have hle : e.offset ≤ l := by
    have h := hactive
    simp [Exec.laneActive, hnm] at h
    exact h.1
  have hmod : (l - e.offset) * 2 % 2 = 0 := by
    rw [Nat.mul_comm]
    exact Nat.mul_mod_right 2 (l - e.offset)
  have hdiv : (l - e.offset) * 2 / 2 = l - e.offset := by
    rw [Nat.mul_comm]
    exact Nat.mul_div_right (l - e.offset) (by decide : 0 < 2)
  simp [stepLoop, h61, h74, writeMaskedWith, Grf.dstIndex, Exec.laneIndex, hnm,
    hdst, Nat.add_sub_of_le hle, hactive, hmod, hdiv]

theorem vaLoopSelLow_value (s : RealState) (j : Nat) :
    (stepLoop s vaLoopSelLow).regs 79 j =
      if s.preds 6 j then s.regs 75 j else s.regs 62 j := by
  unfold vaLoopSelLow
  simp [stepLoop, stepVAL, stepWith, writeVecWith, setReg, readSrcWith, readRegWith,
    srcIndex, vaLoopAlias]

theorem vaLoopSelHigh_value (s : RealState) (j : Nat) :
    (stepLoop s vaLoopSelHigh).regs 80 j =
      if s.preds 6 j then s.regs 76 j else s.regs 63 j := by
  unfold vaLoopSelHigh
  simp [stepLoop, stepVAL, stepWith, writeVecWith, setReg, readSrcWith, readRegWith,
    srcIndex, vaLoopAlias]

theorem vaLoopSelLow_preserves59 (s : RealState) (j : Nat) :
    (stepLoop s vaLoopSelLow).regs 59 j = s.regs 59 j := by
  unfold vaLoopSelLow
  simp [stepLoop, stepVAL, stepWith, writeVecWith, setReg, vaLoopAlias]

theorem vaLoopSelHigh_preserves59 (s : RealState) (j : Nat) :
    (stepLoop s vaLoopSelHigh).regs 59 j = s.regs 59 j := by
  unfold vaLoopSelHigh
  simp [stepLoop, stepVAL, stepWith, writeVecWith, setReg, vaLoopAlias]

theorem vaLoopSelLow_preserves80 (s : RealState) (j : Nat) :
    (stepLoop s vaLoopSelLow).regs 80 j = s.regs 80 j := by
  unfold vaLoopSelLow
  simp [stepLoop, stepVAL, stepWith, writeVecWith, setReg, vaLoopAlias]

theorem vaLoopSelHigh_preserves79 (s : RealState) (j : Nat) :
    (stepLoop s vaLoopSelHigh).regs 79 j = s.regs 79 j := by
  unfold vaLoopSelHigh
  simp [stepLoop, stepVAL, stepWith, writeVecWith, setReg, vaLoopAlias]

theorem vaLoopSelLow_preserves62 (s : RealState) (j : Nat) :
    (stepLoop s vaLoopSelLow).regs 62 j = s.regs 62 j := by
  unfold vaLoopSelLow
  simp [stepLoop, stepVAL, stepWith, writeVecWith, setReg, vaLoopAlias]

theorem vaLoopSelLow_preserves63 (s : RealState) (j : Nat) :
    (stepLoop s vaLoopSelLow).regs 63 j = s.regs 63 j := by
  unfold vaLoopSelLow
  simp [stepLoop, stepVAL, stepWith, writeVecWith, setReg, vaLoopAlias]

theorem vaLoopSelLow_preserves75 (s : RealState) (j : Nat) :
    (stepLoop s vaLoopSelLow).regs 75 j = s.regs 75 j := by
  unfold vaLoopSelLow
  simp [stepLoop, stepVAL, stepWith, writeVecWith, setReg, vaLoopAlias]

theorem vaLoopSelLow_preserves76 (s : RealState) (j : Nat) :
    (stepLoop s vaLoopSelLow).regs 76 j = s.regs 76 j := by
  unfold vaLoopSelLow
  simp [stepLoop, stepVAL, stepWith, writeVecWith, setReg, vaLoopAlias]

theorem vaLoopSelLow_preds (s : RealState) (p j : Nat) :
    (stepLoop s vaLoopSelLow).preds p j = s.preds p j := by
  unfold vaLoopSelLow
  simp [stepLoop, stepVAL, stepWith, writeVecWith]

theorem vaLoopSelects_low (s : RealState) (j : Nat) :
    (runRealWith stepLoop s [vaLoopSelLow, vaLoopSelHigh]).regs 79 j =
      if s.preds 6 j then s.regs 75 j else s.regs 62 j := by
  unfold runRealWith
  simp only [List.foldl_cons, List.foldl_nil]
  rw [vaLoopSelHigh_preserves79, vaLoopSelLow_value]

theorem vaLoopSelects_high (s : RealState) (j : Nat) :
    (runRealWith stepLoop s [vaLoopSelLow, vaLoopSelHigh]).regs 80 j =
      if s.preds 6 j then s.regs 76 j else s.regs 63 j := by
  unfold runRealWith
  simp only [List.foldl_cons, List.foldl_nil]
  rw [vaLoopSelHigh_value, vaLoopSelLow_preserves76, vaLoopSelLow_preserves63,
    vaLoopSelLow_preds]

/-! ## The four writeback moves -/

theorem vaLoopMovLowA_value (s : RealState) (j : Nat) (hj : j < 16) :
    (stepLoop s vaLoopMovLowA).regs 59 (2 * j) = s.regs 79 j := by
  unfold vaLoopMovLowA
  have h := stepLoop_mov_stride2_value s e1Loop dst81Even src79Even
    (by decide) (by decide) rfl rfl j (by
      simp [e1Loop, Exec.laneActive]; omega)
  have hdst : dst81Even.dstIndex (e1Loop.laneIndex j) = 2 * j := by
    rw [e1_laneIndex]; simp [dst81Even, Grf.dstIndex]; omega
  rw [hdst] at h
  have hdnum : vaLoopAlias dst81Even.num = 59 := by decide
  have hsnum : vaLoopAlias src79Even.num = 79 := by decide
  rw [hdnum] at h
  rw [readSrcWith, readRegWith, hsnum, e1_laneIndex] at h
  have hsrc : srcIndex src79Even j = j := by simp [src79Even, srcIndex]
  rw [hsrc] at h
  exact h

theorem vaLoopMovLowB_value (s : RealState) (j : Nat) (h8 : 8 ≤ j) (hj : j < 24) :
    (stepLoop s vaLoopMovLowB).regs 59 (2 * j) = s.regs 79 j := by
  unfold vaLoopMovLowB
  let l := j + 8
  have hactive : e2Loop.laneActive l = true := by
    rw [e2_active]; simp; omega
  have h := stepLoop_movMasked_stride2_value s e2Loop dst81EvenM5 src79EvenM5
    (by decide) (by decide) rfl rfl l hactive
  have hli : e2Loop.laneIndex l = j - 8 := by
    rw [e2_laneIndex]; simp [l]
  have hdst : dst81EvenM5.dstIndex (e2Loop.laneIndex l) = 2 * j := by
    rw [hli]; simp [dst81EvenM5, Grf.dstIndex]; omega
  have hsrcidx : srcIndex src79EvenM5 (j - 8) = j := by
    simp [src79EvenM5, srcIndex]; omega
  rw [hdst] at h
  have hdnum : vaLoopAlias dst81EvenM5.num = 59 := by decide
  have hsnum : vaLoopAlias src79EvenM5.num = 79 := by decide
  rw [hdnum] at h
  rw [readSrcWith, readRegWith, hsnum, hli, hsrcidx] at h
  exact h

theorem vaLoopMovLowB_preserves_lt16 (s : RealState) (d : Nat) (hd : d < 16) :
    (stepLoop s vaLoopMovLowB).regs 59 d = s.regs 59 d := by
  unfold vaLoopMovLowB
  simp [stepLoop, (by decide : src79EvenM5.num ≠ 61),
    (by decide : src79EvenM5.num ≠ 74), writeMaskedWith, dst81EvenM5, vaLoopAlias]
  omega

theorem vaLoopMovLowA_preserves79 (s : RealState) (j : Nat) :
    (stepLoop s vaLoopMovLowA).regs 79 j = s.regs 79 j := by
  unfold vaLoopMovLowA
  have h := stepLoop_mov_preserves_reg (s := s) (e := e1Loop) (dst := dst81Even)
    (src := src79Even) (r := 79) (j := j) (by decide)
  simpa [vaLoopAlias] using h

theorem vaLoopMovHighA_value (s : RealState) (j : Nat) (hj : j < 16) :
    (stepLoop s vaLoopMovHighA).regs 59 (2 * j + 1) = s.regs 80 j := by
  unfold vaLoopMovHighA
  have h := stepLoop_mov_stride2_value s e1Loop dst81Odd src80Odd
    (by decide) (by decide) rfl rfl j (by
      simp [e1Loop, Exec.laneActive]; omega)
  have hdst : dst81Odd.dstIndex (e1Loop.laneIndex j) = 2 * j + 1 := by
    rw [e1_laneIndex]; simp [dst81Odd, Grf.dstIndex]; omega
  rw [hdst] at h
  have hdnum : vaLoopAlias dst81Odd.num = 59 := by decide
  have hsnum : vaLoopAlias src80Odd.num = 80 := by decide
  rw [hdnum] at h
  rw [readSrcWith, readRegWith, hsnum, e1_laneIndex] at h
  have hsrc : srcIndex src80Odd j = j := by simp [src80Odd, srcIndex]
  rw [hsrc] at h
  exact h

theorem vaLoopMovHighB_value (s : RealState) (j : Nat) (h8 : 8 ≤ j) (hj : j < 24) :
    (stepLoop s vaLoopMovHighB).regs 59 (2 * j + 1) = s.regs 80 j := by
  unfold vaLoopMovHighB
  let l := j + 8
  have hactive : e2Loop.laneActive l = true := by
    rw [e2_active]; simp; omega
  have h := stepLoop_movMasked_stride2_value s e2Loop dst81OddM5 src80OddM5
    (by decide) (by decide) rfl rfl l hactive
  have hli : e2Loop.laneIndex l = j - 8 := by
    rw [e2_laneIndex]; simp [l]
  have hdst : dst81OddM5.dstIndex (e2Loop.laneIndex l) = 2 * j + 1 := by
    rw [hli]; simp [dst81OddM5, Grf.dstIndex]; omega
  have hsrcidx : srcIndex src80OddM5 (j - 8) = j := by
    simp [src80OddM5, srcIndex]; omega
  rw [hdst] at h
  have hdnum : vaLoopAlias dst81OddM5.num = 59 := by decide
  have hsnum : vaLoopAlias src80OddM5.num = 80 := by decide
  rw [hdnum] at h
  rw [readSrcWith, readRegWith, hsnum, hli, hsrcidx] at h
  exact h

theorem vaLoopMovHighB_preserves_lt16 (s : RealState) (d : Nat) (hd : d < 16) :
    (stepLoop s vaLoopMovHighB).regs 59 d = s.regs 59 d := by
  unfold vaLoopMovHighB
  simp [stepLoop, (by decide : src80OddM5.num ≠ 61),
    (by decide : src80OddM5.num ≠ 74), writeMaskedWith, dst81OddM5, vaLoopAlias]
  omega

theorem vaLoopMovHighA_preserves80 (s : RealState) (j : Nat) :
    (stepLoop s vaLoopMovHighA).regs 80 j = s.regs 80 j := by
  unfold vaLoopMovHighA
  have h := stepLoop_mov_preserves_reg (s := s) (e := e1Loop) (dst := dst81Odd)
    (src := src80Odd) (r := 80) (j := j) (by decide)
  simpa [vaLoopAlias] using h

theorem vaLoopLowPack_value (s : RealState) (j : Nat) (hj : j < 24) :
    (runRealWith stepLoop s vaLoopLowPack).regs 59 (2 * j) = s.regs 79 j := by
  unfold vaLoopLowPack runRealWith
  simp only [List.foldl_cons, List.foldl_nil]
  by_cases h8 : j < 8
  · rw [vaLoopMovLowB_preserves_lt16 _ (2 * j) (by omega)]
    exact vaLoopMovLowA_value s j (by omega)
  · rw [vaLoopMovLowB_value _ j (by omega) hj]
    exact vaLoopMovLowA_preserves79 s j

theorem vaLoopHighPack_value (s : RealState) (j : Nat) (hj : j < 24) :
    (runRealWith stepLoop s vaLoopHighPack).regs 59 (2 * j + 1) = s.regs 80 j := by
  unfold vaLoopHighPack runRealWith
  simp only [List.foldl_cons, List.foldl_nil]
  by_cases h8 : j < 8
  · rw [vaLoopMovHighB_preserves_lt16 _ (2 * j + 1) (by omega)]
    exact vaLoopMovHighA_value s j (by omega)
  · rw [vaLoopMovHighB_value _ j (by omega) hj]
    exact vaLoopMovHighA_preserves80 s j

theorem vaLoopMovHighA_preserves_even (s : RealState) (d : Nat)
    (heven : d % 2 = 0) :
    (stepLoop s vaLoopMovHighA).regs 59 d = s.regs 59 d := by
  unfold vaLoopMovHighA
  simp [stepLoop, (by decide : src80Odd.num ≠ 61),
    (by decide : src80Odd.num ≠ 74), writeMaskedWith, dst81Odd, vaLoopAlias]
  omega

theorem vaLoopMovHighB_preserves_even (s : RealState) (d : Nat)
    (heven : d % 2 = 0) :
    (stepLoop s vaLoopMovHighB).regs 59 d = s.regs 59 d := by
  unfold vaLoopMovHighB
  simp [stepLoop, (by decide : src80OddM5.num ≠ 61),
    (by decide : src80OddM5.num ≠ 74), writeMaskedWith, dst81OddM5, vaLoopAlias]
  omega

theorem vaLoopHighPack_preserves_even (s : RealState) (d : Nat)
    (heven : d % 2 = 0) :
    (runRealWith stepLoop s vaLoopHighPack).regs 59 d = s.regs 59 d := by
  unfold vaLoopHighPack runRealWith
  simp only [List.foldl_cons, List.foldl_nil]
  rw [vaLoopMovHighB_preserves_even _ d heven,
    vaLoopMovHighA_preserves_even _ d heven]

theorem vaLoopMovLowA_preserves80 (s : RealState) (j : Nat) :
    (stepLoop s vaLoopMovLowA).regs 80 j = s.regs 80 j := by
  unfold vaLoopMovLowA
  have h := stepLoop_mov_preserves_reg (s := s) (e := e1Loop) (dst := dst81Even)
    (src := src79Even) (r := 80) (j := j) (by decide)
  simpa [vaLoopAlias] using h

theorem vaLoopMovLowB_preserves80 (s : RealState) (j : Nat) :
    (stepLoop s vaLoopMovLowB).regs 80 j = s.regs 80 j := by
  unfold vaLoopMovLowB
  have h := stepLoop_movMasked_preserves_reg (s := s) (e := e2Loop)
    (dst := dst81EvenM5) (src := src79EvenM5) (r := 80) (j := j) (by decide)
  simpa [vaLoopAlias] using h

theorem vaLoopLowPack_preserves80 (s : RealState) (j : Nat) :
    (runRealWith stepLoop s vaLoopLowPack).regs 80 j = s.regs 80 j := by
  unfold vaLoopLowPack runRealWith
  simp only [List.foldl_cons, List.foldl_nil]
  rw [vaLoopMovLowB_preserves80, vaLoopMovLowA_preserves80]

theorem vaLoopWriteBack_low (s : RealState) (j : Nat) (hj : j < 24) :
    (runRealWith stepLoop s vaLoopWriteBackSlice).regs 59 (2 * j) = s.regs 79 j := by
  rw [vaLoopWriteBackSlice, runRealWith_append]
  rw [vaLoopHighPack_preserves_even _ (2 * j) (by omega)]
  exact vaLoopLowPack_value s j hj

theorem vaLoopWriteBack_high (s : RealState) (j : Nat) (hj : j < 24) :
    (runRealWith stepLoop s vaLoopWriteBackSlice).regs 59 (2 * j + 1) = s.regs 80 j := by
  rw [vaLoopWriteBackSlice, runRealWith_append]
  rw [vaLoopHighPack_value _ j hj]
  exact vaLoopLowPack_preserves80 s j

theorem vaLoopMovLowA_preserves_ge48 (s : RealState) (d : Nat) (hd : 48 ≤ d) :
    (stepLoop s vaLoopMovLowA).regs 59 d = s.regs 59 d := by
  unfold vaLoopMovLowA
  simp [stepLoop, (by decide : src79Even.num ≠ 61),
    (by decide : src79Even.num ≠ 74), writeMaskedWith, dst81Even, vaLoopAlias,
    e1Loop, Exec.laneActive]
  omega

theorem vaLoopMovLowB_preserves_ge48 (s : RealState) (d : Nat) (hd : 48 ≤ d) :
    (stepLoop s vaLoopMovLowB).regs 59 d = s.regs 59 d := by
  unfold vaLoopMovLowB
  simp [stepLoop, (by decide : src79EvenM5.num ≠ 61),
    (by decide : src79EvenM5.num ≠ 74), writeMaskedWith, dst81EvenM5, vaLoopAlias,
    e2Loop, Exec.laneActive]
  omega

theorem vaLoopMovHighA_preserves_ge48 (s : RealState) (d : Nat) (hd : 48 ≤ d) :
    (stepLoop s vaLoopMovHighA).regs 59 d = s.regs 59 d := by
  unfold vaLoopMovHighA
  simp [stepLoop, (by decide : src80Odd.num ≠ 61),
    (by decide : src80Odd.num ≠ 74), writeMaskedWith, dst81Odd, vaLoopAlias,
    e1Loop, Exec.laneActive]
  omega

theorem vaLoopMovHighB_preserves_ge48 (s : RealState) (d : Nat) (hd : 48 ≤ d) :
    (stepLoop s vaLoopMovHighB).regs 59 d = s.regs 59 d := by
  unfold vaLoopMovHighB
  simp [stepLoop, (by decide : src80OddM5.num ≠ 61),
    (by decide : src80OddM5.num ≠ 74), writeMaskedWith, dst81OddM5, vaLoopAlias,
    e2Loop, Exec.laneActive]
  omega

theorem vaLoopLowPack_preserves_ge48 (s : RealState) (d : Nat) (hd : 48 ≤ d) :
    (runRealWith stepLoop s vaLoopLowPack).regs 59 d = s.regs 59 d := by
  unfold vaLoopLowPack runRealWith
  simp only [List.foldl_cons, List.foldl_nil]
  rw [vaLoopMovLowB_preserves_ge48 _ d hd, vaLoopMovLowA_preserves_ge48 _ d hd]

theorem vaLoopHighPack_preserves_ge48 (s : RealState) (d : Nat) (hd : 48 ≤ d) :
    (runRealWith stepLoop s vaLoopHighPack).regs 59 d = s.regs 59 d := by
  unfold vaLoopHighPack runRealWith
  simp only [List.foldl_cons, List.foldl_nil]
  rw [vaLoopMovHighB_preserves_ge48 _ d hd, vaLoopMovHighA_preserves_ge48 _ d hd]

theorem vaLoopWriteBack_frame_ge48 (s : RealState) (d : Nat) (hd : 48 ≤ d) :
    (runRealWith stepLoop s vaLoopWriteBackSlice).regs 59 d = s.regs 59 d := by
  rw [vaLoopWriteBackSlice, runRealWith_append]
  rw [vaLoopHighPack_preserves_ge48 _ d hd, vaLoopLowPack_preserves_ge48 _ d hd]

theorem vaLoopLoopBack_low (s : RealState) (j : Nat) (hj : j < 24) :
    (runRealWith stepLoop s vaLoopLoopBackSlice).regs 59 (2 * j) =
      if s.preds 6 j then s.regs 75 j else s.regs 62 j := by
  rw [vaLoopLoopBackSlice, runRealWith_append]
  rw [vaLoopWriteBack_low _ j hj, vaLoopSelects_low]

theorem vaLoopLoopBack_high (s : RealState) (j : Nat) (hj : j < 24) :
    (runRealWith stepLoop s vaLoopLoopBackSlice).regs 59 (2 * j + 1) =
      if s.preds 6 j then s.regs 76 j else s.regs 63 j := by
  rw [vaLoopLoopBackSlice, runRealWith_append]
  rw [vaLoopWriteBack_high _ j hj, vaLoopSelects_high]

theorem vaLoopLoopBack_frame_ge48 (s : RealState) (d : Nat) (hd : 48 ≤ d) :
    (runRealWith stepLoop s vaLoopLoopBackSlice).regs 59 d = s.regs 59 d := by
  rw [vaLoopLoopBackSlice, runRealWith_append]
  rw [vaLoopWriteBack_frame_ge48 _ d hd]
  unfold runRealWith
  simp only [List.foldl_cons, List.foldl_nil]
  rw [vaLoopSelHigh_preserves59, vaLoopSelLow_preserves59]

/-! ## Memory frames -/

theorem vaLoopSelLow_mem (s : RealState) :
    (stepLoop s vaLoopSelLow).mem = s.mem := by
  unfold vaLoopSelLow
  simp [stepLoop, stepVAL, stepWith, writeVecWith]

theorem vaLoopSelHigh_mem (s : RealState) :
    (stepLoop s vaLoopSelHigh).mem = s.mem := by
  unfold vaLoopSelHigh
  simp [stepLoop, stepVAL, stepWith, writeVecWith]

theorem vaLoopSelects_mem (s : RealState) :
    (runRealWith stepLoop s [vaLoopSelLow, vaLoopSelHigh]).mem = s.mem := by
  unfold runRealWith
  simp only [List.foldl_cons, List.foldl_nil]
  rw [vaLoopSelHigh_mem, vaLoopSelLow_mem]

theorem vaLoopLowPack_mem (s : RealState) :
    (runRealWith stepLoop s vaLoopLowPack).mem = s.mem := by
  unfold vaLoopLowPack vaLoopMovLowA vaLoopMovLowB runRealWith
  simp only [List.foldl_cons, List.foldl_nil]
  rw [stepLoop_movMasked_mem, stepLoop_mov_mem]

theorem vaLoopHighPack_mem (s : RealState) :
    (runRealWith stepLoop s vaLoopHighPack).mem = s.mem := by
  unfold vaLoopHighPack vaLoopMovHighA vaLoopMovHighB runRealWith
  simp only [List.foldl_cons, List.foldl_nil]
  rw [stepLoop_movMasked_mem, stepLoop_mov_mem]

theorem vaLoopWriteBack_mem (s : RealState) :
    (runRealWith stepLoop s vaLoopWriteBackSlice).mem = s.mem := by
  rw [vaLoopWriteBackSlice, runRealWith_append, vaLoopHighPack_mem, vaLoopLowPack_mem]

theorem vaLoopLoopBack_mem (s : RealState) :
    (runRealWith stepLoop s vaLoopLoopBackSlice).mem = s.mem := by
  rw [vaLoopLoopBackSlice, runRealWith_append, vaLoopWriteBack_mem, vaLoopSelects_mem]

/-! ## Control path -/

/-- At PC 35, a true `P6` falls through to the `_0_010` label at PC 36. -/
theorem vaLoopP6_fallthrough_stepLoop (s : RealState) (lane fuel : Nat)
    (h : s.preds 6 lane = true) :
    runRealCFLaneWith stepLoop vaLoopProgram s 35 (fuel + 1) lane =
      runRealCFLaneWith stepLoop vaLoopProgram s 36 fuel lane := by
  apply runRealCFLane_gotoIf_not_taken stepLoop vaLoopProgram s 35 fuel lane 32 6 true
    "_0_007"
  · exact vaLoopProgram_gotoIf_second
  · simp [h]

/-- PCs 36--43: the `_0_010` label, the two selects, the four pack moves and
the `goto 1 _0_009`. The per-lane interpreter reaches the `_0_009` label at
PC 20 with the loop-back state. -/
theorem vaLoopCFLoopBack (s : RealState) (lane fuel : Nat) :
    runRealCFLaneWith stepLoop vaLoopProgram s 36 (fuel + 8) lane =
      runRealCFLaneWith stepLoop vaLoopProgram
        (runRealWith stepLoop s vaLoopLoopBackSlice) 20 fuel lane := by
  rw [show fuel + 8 = (fuel + 7) + 1 from rfl]
  rw [runRealCFLaneWith_label stepLoop vaLoopProgram s lane 36 (fuel + 7)
    "_0_010" vaLoopProgram_36]
  rw [show fuel + 7 = (fuel + 6) + 1 from rfl]
  rw [runRealCFLaneWith_plain stepLoop vaLoopProgram s lane 37 (fuel + 6)
    vaLoopSelLow vaLoopProgram_37 (by trivial)]
  rw [runRealCFLaneWith_plain stepLoop vaLoopProgram
    (stepLoop s vaLoopSelLow) lane 38 (fuel + 5)
    vaLoopSelHigh vaLoopProgram_38 (by trivial)]
  rw [runRealCFLaneWith_plain stepLoop vaLoopProgram
    (stepLoop (stepLoop s vaLoopSelLow) vaLoopSelHigh) lane 39 (fuel + 4)
    vaLoopMovLowA vaLoopProgram_39 (by trivial)]
  rw [runRealCFLaneWith_plain stepLoop vaLoopProgram
    (stepLoop (stepLoop (stepLoop s vaLoopSelLow) vaLoopSelHigh) vaLoopMovLowA)
    lane 40 (fuel + 3) vaLoopMovLowB vaLoopProgram_40 (by trivial)]
  rw [runRealCFLaneWith_plain stepLoop vaLoopProgram
    (stepLoop (stepLoop (stepLoop (stepLoop s vaLoopSelLow) vaLoopSelHigh)
      vaLoopMovLowA) vaLoopMovLowB) lane 41 (fuel + 2)
    vaLoopMovHighA vaLoopProgram_41 (by trivial)]
  rw [runRealCFLaneWith_plain stepLoop vaLoopProgram
    (stepLoop (stepLoop (stepLoop (stepLoop (stepLoop s vaLoopSelLow)
      vaLoopSelHigh) vaLoopMovLowA) vaLoopMovLowB) vaLoopMovHighA)
    lane 42 (fuel + 1) vaLoopMovHighB vaLoopProgram_42 (by trivial)]
  simp [runRealCFLaneWith, vaLoopProgram_43, vaLoopProgram_label_loop,
    vaLoopLoopBackSlice, vaLoopWriteBackSlice, vaLoopLowPack, vaLoopHighPack,
    runRealWith]

/-! ## The qword `V0059` value after the block -/

/-- The dword view of a qword-per-lane register. -/
def dwordReg (s : RealState) (r : Nat) : DRegs := fun d => (s.regs r d).truncate 32

/-- Pre-loop-back facts, stated as low/high dword equalities. The state is the
PC 36 state: `V0062/V0063` hold the old ID and `V0075/V0076` hold the
incremented ID `old + stride` produced by the `V0072` add and the PC 26--29
packs. -/
structure VaLoopLoopBackPre (s : RealState) (stride : Addr) : Prop where
  oldLow : ∀ l, l < 24 → (s.regs 62 l).truncate 32 = (s.regs 59 l).truncate 32
  oldHigh : ∀ l, l < 24 →
    (s.regs 63 l).truncate 32 = ((s.regs 59 l) >>> 32).truncate 32
  newLow : ∀ l, l < 24 →
    (s.regs 75 l).truncate 32 = ((s.regs 59 l + stride).truncate 32)
  newHigh : ∀ l, l < 24 →
    (s.regs 76 l).truncate 32 = (((s.regs 59 l + stride) >>> 32).truncate 32)

/-- Reassemble a 64-bit value from its two 32-bit halves. This is the same
reconstruction as `writeId24_selected_qword`, proved by bit extensionality so
the module adds no `bv_decide` axiom. -/
theorem qword_merge (v : Addr) :
    ((v.truncate 32).zeroExtend 64 |||
      (((v >>> 32).truncate 32).zeroExtend 64 <<< 32)) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  by_cases hi : i < 64
  · by_cases h32 : i < 32
    · simp [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth, hi, h32]
    · have h32' : ¬ i < 32 := h32
      have hge : 32 ≤ i := by omega
      simp [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth, hi, h32', hge]
      omega
  · simp [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth, hi]

/-- For `l < 24`, the qword view of `V0059` after the loop-back block is the
selected grid-stride ID. -/
theorem vaLoop_loopBack_id (s : RealState) (stride : Addr) (l : Nat) (hl : l < 24)
    (h : VaLoopLoopBackPre s stride) :
    qwordOf (dwordReg (runRealWith stepLoop s vaLoopLoopBackSlice) 59) l =
      selectId (fun k => s.regs 59 k) (fun k => s.regs 59 k + stride)
        (fun k => s.preds 6 k) l := by
  have hlow : (runRealWith stepLoop s vaLoopLoopBackSlice).regs 59 (2 * l) =
      if s.preds 6 l then s.regs 75 l else s.regs 62 l :=
    vaLoopLoopBack_low s l hl
  have hhigh : (runRealWith stepLoop s vaLoopLoopBackSlice).regs 59 (2 * l + 1) =
      if s.preds 6 l then s.regs 76 l else s.regs 63 l :=
    vaLoopLoopBack_high s l hl
  have hlow32 : ((if s.preds 6 l then s.regs 75 l else s.regs 62 l).truncate 32) =
      (selectId (fun k => s.regs 59 k) (fun k => s.regs 59 k + stride)
        (fun k => s.preds 6 k) l).truncate 32 := by
    by_cases hp : s.preds 6 l
    · simp [selectId, hp, h.newLow l hl]
    · simp [selectId, hp, h.oldLow l hl]
  have hhigh32 : ((if s.preds 6 l then s.regs 76 l else s.regs 63 l).truncate 32) =
      ((selectId (fun k => s.regs 59 k) (fun k => s.regs 59 k + stride)
        (fun k => s.preds 6 k) l) >>> 32).truncate 32 := by
    by_cases hp : s.preds 6 l
    · simp [selectId, hp, h.newHigh l hl]
    · simp [selectId, hp, h.oldHigh l hl]
  unfold qwordOf dwordReg
  rw [hlow, hhigh, hlow32, hhigh32]
  exact qword_merge _

/-- On a taken lane the loop-back value is the incremented ID. -/
theorem vaLoop_loopBack_id_taken (s : RealState) (stride : Addr) (l : Nat)
    (hl : l < 24) (h : VaLoopLoopBackPre s stride)
    (htake : s.preds 6 l = true) :
    qwordOf (dwordReg (runRealWith stepLoop s vaLoopLoopBackSlice) 59) l =
      s.regs 59 l + stride := by
  rw [vaLoop_loopBack_id s stride l hl h]
  exact selectId_true _ _ _ l htake

/-- On a kept lane the loop-back value is the old ID. -/
theorem vaLoop_loopBack_id_kept (s : RealState) (stride : Addr) (l : Nat)
    (hl : l < 24) (h : VaLoopLoopBackPre s stride)
    (hkeep : s.preds 6 l = false) :
    qwordOf (dwordReg (runRealWith stepLoop s vaLoopLoopBackSlice) 59) l =
      s.regs 59 l := by
  rw [vaLoop_loopBack_id s stride l hl h]
  exact selectId_false _ _ _ l hkeep

/-! ## Lanes 24--31 and the dword-slot boundary -/

/-- The qword view of `V0059` is unchanged on lanes 24--31: the pack touches
only dword slots 0..47, while qword lane `l >= 24` reads dwords `2*l` and
`2*l+1`, both at least 48. -/
theorem vaLoop_loopBack_qword_frame_ge24 (s : RealState) (l : Nat) (hl : 24 ≤ l) :
    qwordOf (dwordReg (runRealWith stepLoop s vaLoopLoopBackSlice) 59) l =
      qwordOf (dwordReg s 59) l := by
  unfold qwordOf dwordReg
  rw [vaLoopLoopBack_frame_ge48 _ (2 * l) (by omega),
    vaLoopLoopBack_frame_ge48 _ (2 * l + 1) (by omega)]

/-- A state used only to exhibit the dword-slot boundary: `V0062` lane 12 is 1
and every other slot is 0. -/
def vaLoopCounterState : RealState where
  regs := fun r e => if r = 62 ∧ e = 12 then 1 else 0
  preds := fun _ _ => false
  mem := fun _ => 0
  halted := false

/-- The naive all-32-lane statement `regs 59 l` is false: the pack writes
dword slot 24, which is not qword lane 24. -/
theorem vaLoopLoopBack_dword_counterexample :
    ∃ s : RealState, ∃ l : Nat, 24 ≤ l ∧
      (runRealWith stepLoop s vaLoopLoopBackSlice).regs 59 l ≠ s.regs 59 l := by
  refine ⟨vaLoopCounterState, 24, by omega, ?_⟩
  rw [vaLoopLoopBack_low vaLoopCounterState 12 (by omega)]
  simp [vaLoopCounterState]

/-! ## Model boundary for a literal second iteration

`vaLoop_loopBack_id` is the qword-view statement: `dwordReg` and `qwordOf`
coalesce the four writeback moves into `V0059` lanes. The literal body at
PC 21 reads `s.regs 59 l` directly, and after the writeback that slot holds
dword `l`, not qword lane `l`; `vaLoopLoopBack_dword_counterexample` exhibits
the difference at `l = 24`. Consequently a fully literal two-iteration store
theorem needs a dword/qword aliasing (or coalescing) step in `RealState` at
the loop-back. `vaLoop_lane_second_body` proves the intended value-level
grid-stride store on `vaLoopReentry`, the state whose `V0059` lanes are the
selected IDs.
-/

/-! ## Value-level re-entry and the second body -/

/-- The value-level re-entry index: selected ID on lanes 0..23 and the old
value elsewhere. -/
def vaLoopReentryId (s : RealState) (old : Nat → Addr) (stride : Addr) : Nat → Addr :=
  fun l => if l < 24 then
    selectId old (fun k => old k + stride) (fun k => s.preds 6 k) l
  else old l

/-- A value-level state whose `V0059` qword lanes carry the selected IDs. -/
def vaLoopReentry (s : RealState) (old : Nat → Addr) (stride : Addr) : RealState :=
  { s with regs := fun r e =>
      if r = 59 then vaLoopReentryId s old stride e else s.regs r e }

theorem vaLoopReentry_mem (s : RealState) (old : Nat → Addr) (stride : Addr) :
    (vaLoopReentry s old stride).mem = s.mem := by
  simp [vaLoopReentry]

theorem vaLoopReentry_bodyPre (s : RealState) (aPtr bPtr cPtr : Addr)
    (old : Nat → Addr) (stride : Addr)
    (h : VaLoopBodyPre s aPtr bPtr cPtr old) :
    VaLoopBodyPre (vaLoopReentry s old stride) aPtr bPtr cPtr
      (vaLoopReentryId s old stride) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [vaLoopReentry] using h.aReg
  · simpa [vaLoopReentry] using h.bReg
  · simpa [vaLoopReentry] using h.cReg
  · intro l
    simp [vaLoopReentry]

/-- The value-level second body, with the index supplied by `vaLoopReentryId`.
The memory-safety hypotheses are for that updated index. -/
theorem vaLoopReentry_body_store (s : RealState) (aPtr bPtr cPtr : Addr)
    (old : Nat → Addr) (stride : Addr)
    (h : VaLoopBodyPre s aPtr bPtr cPtr old) (l : Nat) (hl : l < 32)
    (ha : aPtr.toNat % 4 = 0) (hb : bPtr.toNat % 4 = 0)
    (hc : cPtr.toNat % 4 = 0)
    (hab : aPtr.toNat + 4 * (vaLoopReentryId s old stride l).toNat < 2 ^ 64)
    (hbb : bPtr.toNat + 4 * (vaLoopReentryId s old stride l).toNat < 2 ^ 64)
    (hcb : cPtr.toNat + 4 * (vaLoopReentryId s old stride l).toNat < 2 ^ 64)
    (hboundC : ∀ k, k < 32 →
      cPtr.toNat + 4 * (vaLoopReentryId s old stride k).toNat < 2 ^ 64)
    (hdistinct : ∀ k, k < 32 → k ≠ l →
      cPtr.toNat / 4 + (vaLoopReentryId s old stride k).toNat ≠
        cPtr.toNat / 4 + (vaLoopReentryId s old stride l).toNat) :
    (runRealWith stepLoop (vaLoopReentry s old stride) vaLoopBodySlice).mem
        (cPtr.toNat / 4 + (vaLoopReentryId s old stride l).toNat) =
      s.mem (aPtr.toNat / 4 + (vaLoopReentryId s old stride l).toNat) +
        s.mem (bPtr.toNat / 4 + (vaLoopReentryId s old stride l).toNat) := by
  have hpre := vaLoopReentry_bodyPre s aPtr bPtr cPtr old stride h
  have hstore := vaLoopBodySlice_store_at (vaLoopReentry s old stride)
    aPtr bPtr cPtr (vaLoopReentryId s old stride) hpre l hl ha hb hc hab hbb hcb
    hboundC hdistinct
  rwa [vaLoopReentry_mem] at hstore

/-- On a lane where `P6` is true, the value-level index is exactly
`old l + stride`, the next grid-stride address. -/
theorem vaLoopReentryId_eq_add (s : RealState) (old : Nat → Addr) (stride : Addr)
    (l : Nat) (hl : l < 24) (htake : s.preds 6 l = true) :
    vaLoopReentryId s old stride l = old l + stride := by
  simp [vaLoopReentryId, hl, selectId, htake]

/-- The second body stores `C[id + stride] = A[id + stride] + B[id + stride]`
on the value-level re-entry state. -/
theorem vaLoopReentry_second_store (s : RealState) (aPtr bPtr cPtr : Addr)
    (old : Nat → Addr) (stride : Addr)
    (h : VaLoopBodyPre s aPtr bPtr cPtr old) (l : Nat) (hl : l < 24)
    (htake : s.preds 6 l = true)
    (ha : aPtr.toNat % 4 = 0) (hb : bPtr.toNat % 4 = 0)
    (hc : cPtr.toNat % 4 = 0)
    (hab : aPtr.toNat + 4 * (old l + stride).toNat < 2 ^ 64)
    (hbb : bPtr.toNat + 4 * (old l + stride).toNat < 2 ^ 64)
    (hcb : cPtr.toNat + 4 * (old l + stride).toNat < 2 ^ 64)
    (hboundC : ∀ k, k < 32 →
      cPtr.toNat + 4 * (vaLoopReentryId s old stride k).toNat < 2 ^ 64)
    (hdistinct : ∀ k, k < 32 → k ≠ l →
      cPtr.toNat / 4 + (vaLoopReentryId s old stride k).toNat ≠
        cPtr.toNat / 4 + (old l + stride).toNat) :
    (runRealWith stepLoop (vaLoopReentry s old stride) vaLoopBodySlice).mem
        (cPtr.toNat / 4 + (old l + stride).toNat) =
      s.mem (aPtr.toNat / 4 + (old l + stride).toNat) +
        s.mem (bPtr.toNat / 4 + (old l + stride).toNat) := by
  have hidx := vaLoopReentryId_eq_add s old stride l hl htake
  have hstore := vaLoopReentry_body_store s aPtr bPtr cPtr old stride h l (by omega)
    ha hb hc (by rwa [hidx]) (by rwa [hidx]) (by rwa [hidx]) hboundC (by rwa [hidx])
  rwa [hidx] at hstore

/-- The bridge from the decoded block to the value-level re-entry state: for
`l < 24`, the qword view of the executed block equals the re-entry lane. -/
theorem vaLoop_loopBack_qword_reentry (s : RealState) (old : Nat → Addr)
    (stride : Addr) (l : Nat) (hl : l < 24)
    (hidx : ∀ k, s.regs 59 k = old k) (h : VaLoopLoopBackPre s stride) :
    qwordOf (dwordReg (runRealWith stepLoop s vaLoopLoopBackSlice) 59) l =
      vaLoopReentryId s old stride l := by
  rw [vaLoop_loopBack_id s stride l hl h]
  simp [vaLoopReentryId, hl, hidx]

/-- A lane with `P6 = true` at PC 35 falls through to PC 36, executes the
loop-back block, re-enters at PC 20/21, and the value-level second body stores
`C[id + stride] = A[id + stride] + B[id + stride]`. -/
theorem vaLoop_lane_second_body (s : RealState) (lane fuel : Nat)
    (aPtr bPtr cPtr : Addr) (old : Nat → Addr) (stride : Addr)
    (h : VaLoopBodyPre s aPtr bPtr cPtr old)
    (hP6 : s.preds 6 lane = true) (hl : lane < 24)
    (ha : aPtr.toNat % 4 = 0) (hb : bPtr.toNat % 4 = 0)
    (hc : cPtr.toNat % 4 = 0)
    (hab : aPtr.toNat + 4 * (old lane + stride).toNat < 2 ^ 64)
    (hbb : bPtr.toNat + 4 * (old lane + stride).toNat < 2 ^ 64)
    (hcb : cPtr.toNat + 4 * (old lane + stride).toNat < 2 ^ 64)
    (hboundC : ∀ k, k < 32 →
      cPtr.toNat + 4 * (vaLoopReentryId s old stride k).toNat < 2 ^ 64)
    (hdistinct : ∀ k, k < 32 → k ≠ lane →
      cPtr.toNat / 4 + (vaLoopReentryId s old stride k).toNat ≠
        cPtr.toNat / 4 + (old lane + stride).toNat)
    (hloop : VaLoopLoopBackPre s stride) :
    (runRealCFLaneWith stepLoop vaLoopProgram s 35 (fuel + 10) lane =
      runRealCFLaneWith stepLoop vaLoopProgram
        (runRealWith stepLoop s vaLoopLoopBackSlice) 21 fuel lane) ∧
    (qwordOf (dwordReg (runRealWith stepLoop s vaLoopLoopBackSlice) 59) lane =
      vaLoopReentryId s old stride lane) ∧
    ((runRealWith stepLoop (vaLoopReentry s old stride) vaLoopBodySlice).mem
        (cPtr.toNat / 4 + (old lane + stride).toNat) =
      s.mem (aPtr.toNat / 4 + (old lane + stride).toNat) +
        s.mem (bPtr.toNat / 4 + (old lane + stride).toNat)) := by
  have hpath : runRealCFLaneWith stepLoop vaLoopProgram s 35 (fuel + 10) lane =
      runRealCFLaneWith stepLoop vaLoopProgram
        (runRealWith stepLoop s vaLoopLoopBackSlice) 21 fuel lane := by
    rw [show fuel + 10 = (fuel + 9) + 1 from rfl]
    rw [vaLoopP6_fallthrough_stepLoop s lane (fuel + 9) hP6]
    rw [show fuel + 9 = (fuel + 1) + 8 from rfl]
    rw [vaLoopCFLoopBack s lane (fuel + 1)]
    rw [runRealCFLaneWith_label stepLoop vaLoopProgram _ lane 20 fuel "_0_009"
      (by decide)]
  have hqword := vaLoop_loopBack_qword_reentry s old stride lane hl h.idxReg hloop
  have hstore := vaLoopReentry_second_store s aPtr bPtr cPtr old stride h lane hl hP6
    ha hb hc hab hbb hcb hboundC hdistinct
  exact ⟨hpath, hqword, hstore⟩

/-! ## Grid-stride reading -/

/-- The loop-back step is the grid-stride step `strideId old stride 1`. -/
theorem vaLoop_loopBack_is_strideId (old : Addr) (stride : Addr) :
    old + stride = strideId old stride 1 := by
  rw [strideId_one]

end

end IntelGpu
