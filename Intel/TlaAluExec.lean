-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaAlu
public import Intel.TlaMovExec

@[expose] public section

/-!
# Executing the predicated SYCL-TLA ALU forms

`Intel/TlaAlu` decodes the `and`/`add`/`mad` forms. This module executes the
register-destination subset on the logical register file: `and`, `add` and
`mad` write their active destination elements, and every other operation is
left unmodelled (`none`).

The three prologue ALU instructions are worked out:
`r127.2 = r0.0 & 0xFFFFFFC0`, `r127.2 = r127.2 + 0x280`, and
`r127.0 = r127.2 * r127.0 + 0x40`.
-/

namespace IntelGpu

/-- Execute one decoded ALU instruction, for the modelled operations. -/
def tlaAluStep? (rf : RegFile) (a : TlaAlu) : Option RegFile :=
  match a.dst with
  | .r d =>
      let f := readTlaSrc rf a.src1
      let g := readTlaSrc rf a.src2
      match a.op with
      | .and => some (writeTlaMasked rf d a.exec (fun i => f i &&& g i))
      | .add => some (writeTlaMasked rf d a.exec (fun i => f i + g i))
      | .mul => some (writeTlaMasked rf d a.exec (fun i => f i * g i))
      | .or => some (writeTlaMasked rf d a.exec (fun i => f i ||| g i))
      | .shl => some (writeTlaMasked rf d a.exec (fun i => f i <<< (g i).toNat))
      | .shr => some (writeTlaMasked rf d a.exec (fun i => f i >>> (g i).toNat))
      | .asr => some (writeTlaMasked rf d a.exec
          (fun i => (f i).sshiftRight (g i).toNat))
      | .mad =>
          match a.src3 with
          | some s3 =>
              some (writeTlaMasked rf d a.exec
                (fun i => f i * g i + readTlaSrc rf s3 i))
          | none => none
      | _ => none
  | _ => none

theorem tlaAluStep?_and (rf : RegFile) (e : Exec) (d : Grf) (s1 s2 : TlaSrc) :
    tlaAluStep? rf ⟨.and, e, .r d, s1, s2, none⟩ =
      some (writeTlaMasked rf d e
        (fun i => readTlaSrc rf s1 i &&& readTlaSrc rf s2 i)) := rfl

theorem tlaAluStep?_add (rf : RegFile) (e : Exec) (d : Grf) (s1 s2 : TlaSrc) :
    tlaAluStep? rf ⟨.add, e, .r d, s1, s2, none⟩ =
      some (writeTlaMasked rf d e
        (fun i => readTlaSrc rf s1 i + readTlaSrc rf s2 i)) := rfl

theorem tlaAluStep?_mad (rf : RegFile) (e : Exec) (d : Grf) (s1 s2 s3 : TlaSrc) :
    tlaAluStep? rf ⟨.mad, e, .r d, s1, s2, some s3⟩ =
      some (writeTlaMasked rf d e
        (fun i => readTlaSrc rf s1 i * readTlaSrc rf s2 i + readTlaSrc rf s3 i)) := rfl

theorem tlaAluStep?_mul (rf : RegFile) (e : Exec) (d : Grf) (s1 s2 : TlaSrc) :
    tlaAluStep? rf ⟨.mul, e, .r d, s1, s2, none⟩ =
      some (writeTlaMasked rf d e
        (fun i => readTlaSrc rf s1 i * readTlaSrc rf s2 i)) := rfl

theorem tlaAluStep?_or (rf : RegFile) (e : Exec) (d : Grf) (s1 s2 : TlaSrc) :
    tlaAluStep? rf ⟨.or, e, .r d, s1, s2, none⟩ =
      some (writeTlaMasked rf d e
        (fun i => readTlaSrc rf s1 i ||| readTlaSrc rf s2 i)) := rfl

theorem tlaAluStep?_shl (rf : RegFile) (e : Exec) (d : Grf) (s1 s2 : TlaSrc) :
    tlaAluStep? rf ⟨.shl, e, .r d, s1, s2, none⟩ =
      some (writeTlaMasked rf d e
        (fun i => readTlaSrc rf s1 i <<< (readTlaSrc rf s2 i).toNat)) := rfl

theorem tlaAluStep?_shr (rf : RegFile) (e : Exec) (d : Grf) (s1 s2 : TlaSrc) :
    tlaAluStep? rf ⟨.shr, e, .r d, s1, s2, none⟩ =
      some (writeTlaMasked rf d e
        (fun i => readTlaSrc rf s1 i >>> (readTlaSrc rf s2 i).toNat)) := rfl

theorem tlaAluStep?_asr (rf : RegFile) (e : Exec) (d : Grf) (s1 s2 : TlaSrc) :
    tlaAluStep? rf ⟨.asr, e, .r d, s1, s2, none⟩ =
      some (writeTlaMasked rf d e
        (fun i => (readTlaSrc rf s1 i).sshiftRight (readTlaSrc rf s2 i).toNat)) := rfl

theorem tlaAluStep?_mach_none (rf : RegFile) (e : Exec) (d : Grf) (s1 s2 : TlaSrc) :
    tlaAluStep? rf ⟨.mach, e, .r d, s1, s2, none⟩ = none := rfl

/-- An active unit-stride write returns the source value. -/
theorem writeTlaMasked_self_active (rf : RegFile) (g : Grf) (e : Exec)
    (f : Nat → Word) (j : Nat) (hb : g.row * 8 + g.col ≤ j)
    (hd : g.hstride = 1)
    (ha : e.laneActive (if e.noMask then j - (g.row * 8 + g.col)
      else e.offset + (j - (g.row * 8 + g.col))) = true) :
    writeTlaMasked rf g e f g.num j = f (j - (g.row * 8 + g.col)) := by
  unfold writeTlaMasked
  simp [hd, hb, ha]

/-- The prologue mask: `r127.2 = r0.0 & 0xFFFFFFC0`. -/
def prologueAnd : TlaAlu :=
  ⟨.and, ⟨1, 0, true⟩, .r ⟨127, 0, 2, 1, 1, 1⟩,
    .reg ⟨0, 0, 0, 0, 1, 0⟩, .imm (0xFFFFFFC0 : Int) .ud, none⟩

/-- The prologue add: `r127.2 = r127.2 + 0x280`. -/
def prologueAdd : TlaAlu :=
  ⟨.add, ⟨1, 0, true⟩, .r ⟨127, 0, 2, 1, 1, 1⟩,
    .reg ⟨127, 0, 2, 0, 1, 0⟩, .imm (0x280 : Int) .ud, none⟩

/-- The prologue multiply-add: `r127.0 = r127.2 * r127.0 + 0x40`. -/
def prologueMad : TlaAlu :=
  ⟨.mad, ⟨1, 0, true⟩, .r ⟨127, 0, 0, 1, 1, 1⟩,
    .reg ⟨127, 0, 2, 0, 1, 0⟩, .reg ⟨127, 0, 0, 0, 1, 0⟩,
    some (.imm (0x40 : Int) .w16)⟩

theorem prologue_and_value (rf : RegFile) :
    ∃ rf', tlaAluStep? rf prologueAnd = some rf' ∧
      rf' 127 2 = rf 0 0 &&& 0xFFFFFFC0 := by
  refine ⟨writeTlaMasked rf ⟨127, 0, 2, 1, 1, 1⟩ ⟨1, 0, true⟩
    (fun i => readTlaSrc rf (.reg ⟨0, 0, 0, 0, 1, 0⟩) i &&&
      readTlaSrc rf (.imm (0xFFFFFFC0 : Int) .ud) i), ?_, ?_⟩
  · rfl
  · rw [writeTlaMasked_self_active rf ⟨127, 0, 2, 1, 1, 1⟩ ⟨1, 0, true⟩ _ 2
      (by decide) rfl (by decide)]
    simp [readTlaSrc, srcIndex]

theorem prologue_add_value (rf : RegFile) :
    ∃ rf', tlaAluStep? rf prologueAdd = some rf' ∧
      rf' 127 2 = rf 127 2 + 0x280 := by
  refine ⟨writeTlaMasked rf ⟨127, 0, 2, 1, 1, 1⟩ ⟨1, 0, true⟩
    (fun i => readTlaSrc rf (.reg ⟨127, 0, 2, 0, 1, 0⟩) i +
      readTlaSrc rf (.imm (0x280 : Int) .ud) i), ?_, ?_⟩
  · rfl
  · rw [writeTlaMasked_self_active rf ⟨127, 0, 2, 1, 1, 1⟩ ⟨1, 0, true⟩ _ 2
      (by decide) rfl (by decide)]
    simp [readTlaSrc, srcIndex]

theorem prologue_mad_value (rf : RegFile) :
    ∃ rf', tlaAluStep? rf prologueMad = some rf' ∧
      rf' 127 0 = rf 127 2 * rf 127 0 + 0x40 := by
  refine ⟨writeTlaMasked rf ⟨127, 0, 0, 1, 1, 1⟩ ⟨1, 0, true⟩
    (fun i => readTlaSrc rf (.reg ⟨127, 0, 2, 0, 1, 0⟩) i *
      readTlaSrc rf (.reg ⟨127, 0, 0, 0, 1, 0⟩) i +
      readTlaSrc rf (.imm (0x40 : Int) .w16) i), ?_, ?_⟩
  · rfl
  · rw [writeTlaMasked_self_active rf ⟨127, 0, 0, 1, 1, 1⟩ ⟨1, 0, true⟩ _ 0
      (by decide) rfl (by decide)]
    simp [readTlaSrc, srcIndex]

set_option maxRecDepth 100000 in
/-- 54 of the 109 ALU instructions are in the executed subset. -/
theorem tlaAlu_modeled_count :
    (realTlaGemmAlu.filter
      (fun a => (tlaAluStep? (fun _ _ => 0) a).isSome)).length = 54 := by
  decide

end IntelGpu
