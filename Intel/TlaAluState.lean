-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaAluExec

@[expose] public section

/-!
# Multi-bank state for the SYCL-TLA scalar ALU

`Intel/TlaAlu` has `r`, `acc`, `a`, `cr` and `f` destinations; `Intel.TlaAluExec`
models only the `r` bank. This module adds a `TlaState` with the five banks and
executes the modelled operations on all of them. The worked examples are
`mul acc0, r1.13, r1.20`, `shr a0.2, r1.9, 4` and `or cr0, cr0, 0x400004C0`.
-/

namespace IntelGpu

structure TlaState where
  regs : RegFile
  acc : Nat → Nat → Word
  addr : Nat → Nat → Word
  cr : Nat → Nat → Word
  flags : Nat → Nat → Word

def readTlaSrcState (st : TlaState) : TlaSrc → Nat → Word
  | .reg g => fun i => st.regs g.num (srcIndex g i)
  | .cr n sub => fun _ => st.cr n sub
  | .imm v _ => fun _ => BitVec.ofInt 32 v

def writeBank (f : Nat → Nat → Word) (n sub : Nat) (v : Word) : Nat → Nat → Word :=
  fun n' j => if n' = n ∧ j = sub then v else f n' j

theorem writeBank_same (f : Nat → Nat → Word) (n sub : Nat) (v : Word) :
    writeBank f n sub v n sub = v := by
  simp [writeBank]

theorem writeBank_other (f : Nat → Nat → Word) (n sub n' j : Nat) (v : Word)
    (h : n' ≠ n ∨ j ≠ sub) :
    writeBank f n sub v n' j = f n' j := by
  have h' : ¬ (n' = n ∧ j = sub) := by
    rintro ⟨h1, h2⟩
    rcases h with h | h
    · exact h h1
    · exact h h2
  simp [writeBank, h']

def tlaAluFun : TlaAluOp → (Nat → Word) → (Nat → Word) → (Nat → Word) →
    Option (Nat → Word)
  | .and, f, g, _ => some (fun i => f i &&& g i)
  | .add, f, g, _ => some (fun i => f i + g i)
  | .mul, f, g, _ => some (fun i => f i * g i)
  | .or, f, g, _ => some (fun i => f i ||| g i)
  | .shl, f, g, _ => some (fun i => f i <<< (g i).toNat)
  | .shr, f, g, _ => some (fun i => f i >>> (g i).toNat)
  | .asr, f, g, _ => some (fun i => (f i).sshiftRight (g i).toNat)
  | .mad, f, g, h => some (fun i => f i * g i + h i)
  | .mach, f, g, _ => some (fun i => BitVec.ofNat 32 ((f i).toNat * (g i).toNat >>> 32))
  | .macl, f, g, _ => some (fun i => BitVec.ofNat 32 ((f i).toNat * (g i).toNat))

def tlaAluStateStep? (st : TlaState) (a : TlaAlu) : Option TlaState :=
  let f := readTlaSrcState st a.src1
  let g := readTlaSrcState st a.src2
  let h := match a.src3 with
    | some s => readTlaSrcState st s
    | none => fun _ => 0
  match tlaAluFun a.op f g h with
  | none => none
  | some r =>
      match a.dst with
      | .r d => some { st with regs := writeTlaMasked st.regs d a.exec r }
      | .acc n sub => some { st with acc := writeBank st.acc n sub (r 0) }
      | .addr n sub => some { st with addr := writeBank st.addr n sub (r 0) }
      | .cr n sub => some { st with cr := writeBank st.cr n sub (r 0) }
      | .flag n sub => some { st with flags := writeBank st.flags n sub (r 0) }

/-- `mul acc0, r1.13, r1.20`. -/
def mulAcc : TlaAlu :=
  ⟨.mul, ⟨1, 0, true⟩, .acc 0 0,
    .reg ⟨1, 0, 13, 0, 1, 0⟩, .reg ⟨1, 0, 20, 0, 1, 0⟩, none⟩

/-- `shr a0.2, r1.9, 4`. -/
def shrAddr : TlaAlu :=
  ⟨.shr, ⟨1, 0, true⟩, .addr 0 2,
    .reg ⟨1, 0, 9, 0, 1, 0⟩, .imm (4 : Int) .ud, none⟩

/-- `or cr0, cr0, 0x400004C0`. -/
def orCr : TlaAlu :=
  ⟨.or, ⟨1, 0, true⟩, .cr 0 0,
    .cr 0 0, .imm (0x400004C0 : Int) .ud, none⟩

theorem mul_acc_value (st : TlaState) :
    ∃ st', tlaAluStateStep? st mulAcc = some st' ∧
      st'.acc 0 0 = st.regs 1 13 * st.regs 1 20 ∧ st'.regs = st.regs := by
  refine ⟨_, rfl, ?_, rfl⟩
  simp [mulAcc, tlaAluStateStep?, tlaAluFun, readTlaSrcState, srcIndex, writeBank]

theorem shr_addr_value (st : TlaState) :
    ∃ st', tlaAluStateStep? st shrAddr = some st' ∧
      st'.addr 0 2 = st.regs 1 9 >>> (4 : Word).toNat ∧ st'.regs = st.regs := by
  refine ⟨_, rfl, ?_, rfl⟩
  simp [shrAddr, tlaAluStateStep?, tlaAluFun, readTlaSrcState, srcIndex, writeBank]

theorem or_cr_value (st : TlaState) :
    ∃ st', tlaAluStateStep? st orCr = some st' ∧
      st'.cr 0 0 = st.cr 0 0 ||| 0x400004C0 ∧ st'.regs = st.regs := by
  refine ⟨_, rfl, ?_, rfl⟩
  simp [orCr, tlaAluStateStep?, tlaAluFun, readTlaSrcState, writeBank]

end IntelGpu
