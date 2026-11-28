-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaCmpCond

@[expose] public section

/-!
# The `sel` instruction

The FMHA prefill kernel uses `sel` to pick between two values under a flag:

* `(W) sel (1|M0) (ge)f0.0 r1.10<1>:d r1.12<0;1,0>:d 0:w`,
* `sel (16|M0) (lt)f0.0 r66.0<1>:f r66.0<1;1,0>:f acc0.0<1;1,0>:f`,
* `(f3.1) sel (16|M0) acc0.0<1>:f r2.2<0;1,0>:f 0xFF800000:f`.

The destination may be a GRF region or an `acc`/`a`/`cr`/`f` bank element,
and a source may be an accumulator-bank element (`acc0.0`), which the plain
`TlaSrc` does not cover; `TlaSelSrc` adds that case.
-/

namespace IntelGpu

/-- A `sel` source: a plain TLA source or an accumulator-bank element. -/
inductive TlaSelSrc where
  | src (s : TlaSrc)
  | acc (n sub : Nat)
  deriving Repr, DecidableEq

/-- Parse a `sel` source, including `accN.M`. -/
def parseSelSrc (s : String) : Option TlaSelSrc :=
  match (operandCore s).toList with
  | 'a' :: 'c' :: 'c' :: _ =>
      match numRuns (operandCore s) with
      | n :: sub :: _ => some (.acc n sub)
      | _ => none
  | _ => (parseTlaSrc s).map .src

/-- A decoded `sel` instruction. -/
structure TlaSel where
  predOp : String
  exec : Exec
  cond : String
  dst : TlaAluDst
  src1 : TlaSelSrc
  src2 : TlaSelSrc
  deriving Repr, DecidableEq

/-- Parse `sel (cond) dst a b` in its three printed spellings. -/
def parseTlaSelInstr : TlaInstr → Option TlaSel
  | .plain "sel" (e :: cond :: dst :: a :: b :: _) =>
      match parseTlaExec e, parseTlaAluDst dst, parseSelSrc a, parseSelSrc b with
      | some ex, some d, some x, some y => some ⟨"", ex, cond, d, x, y⟩
      | _, _, _, _ => none
  | .predicated "(W) sel" (e :: cond :: dst :: a :: b :: _) =>
      match parseTlaExec e, parseTlaAluDst dst, parseSelSrc a, parseSelSrc b with
      | some ex, some d, some x, some y => some ⟨"(W)", ex, cond, d, x, y⟩
      | _, _, _, _ => none
  | .predicated op (e :: dst :: a :: b :: _) =>
      if listHasPrefix "(".toList op.toList ∧ listHasPrefix " sel".toList.reverse op.toList.reverse then
        match parseTlaExec e, parseTlaAluDst dst, parseSelSrc a, parseSelSrc b with
        | some ex, some d, some x, some y =>
            some ⟨String.ofList (op.toList.take (op.toList.length - 4)), ex, "", d, x, y⟩
        | _, _, _, _ => none
      else none
  | _ => none

/-- The flag a `sel` tests: the `(op)fN.M` condition, or the outer
predicate `(fN.M)`. -/
def TlaSel.flag? (s : TlaSel) : Option (Nat × Nat) :=
  match parseCmpFlag s.cond with
  | some (_, n, m) => some (n, m)
  | none =>
      match numRuns s.predOp with
      | [n, m] => some (n, m)
      | _ => none

/-- Read a `sel` source at a lane. -/
def readSelSrc (st : TlaState) : TlaSelSrc → Nat → Word
  | .src s => readTlaSrcState st s
  | .acc n sub => fun _ => st.acc n sub

/-- The selected value at a lane. -/
def TlaSel.value (st : TlaState) (s : TlaSel) (i : Nat) : Word :=
  match s.flag? with
  | some (n, m) => if st.flags n m = 0 then readSelSrc st s.src2 i else readSelSrc st s.src1 i
  | none => readSelSrc st s.src1 i

/-- Execute a `sel` on the multi-bank state. -/
def TlaSel.step (st : TlaState) (s : TlaSel) : TlaState :=
  let v : Nat → Word := s.value st
  match s.dst with
  | .r g => { st with regs := writeTlaMasked st.regs g s.exec v }
  | .acc n sub => { st with acc := writeBank st.acc n sub (v 0) }
  | .addr n sub => { st with addr := writeBank st.addr n sub (v 0) }
  | .cr n sub => { st with cr := writeBank st.cr n sub (v 0) }
  | .flag n sub => { st with flags := writeBank st.flags n sub (v 0) }

set_option maxRecDepth 100000 in
theorem parseTlaSel_plain :
    parseTlaSelInstr (.plain "sel"
      ["(16|M0)", "(lt)f0.0", "r66.0<1>:f", "r66.0<1;1,0>:f", "acc0.0<1;1,0>:f", "{Compacted}"]) =
      some ⟨"", ⟨16, 0, true⟩, "(lt)f0.0", .r ⟨66, 0, 0, 1, 1, 1⟩,
        .src (.reg ⟨66, 0, 0, 1, 1, 0⟩), .acc 0 0⟩ := by decide

set_option maxRecDepth 100000 in
theorem parseTlaSel_W :
    parseTlaSelInstr (.predicated "(W) sel"
      ["(1|M0)", "(ge)f0.0", "r1.10<1>:d", "r1.12<0;1,0>:d", "0:w", "{I@5}"]) =
      some ⟨"(W)", ⟨1, 0, true⟩, "(ge)f0.0", .r ⟨1, 0, 10, 1, 1, 1⟩,
        .src (.reg ⟨1, 0, 12, 0, 1, 0⟩), .src (.imm 0 .w16)⟩ := by decide

set_option maxRecDepth 100000 in
theorem parseTlaSel_outer :
    parseTlaSelInstr (.predicated "(f3.1) sel"
      ["(16|M0)", "acc0.0<1>:f", "r2.2<0;1,0>:f", "0xFF800000:f", "{Compacted}"]) =
      some ⟨"(f3.1)", ⟨16, 0, true⟩, "", .acc 0 0,
        .src (.reg ⟨2, 0, 2, 0, 1, 0⟩), .src (.imm 4286578688 .d32)⟩ := by decide

theorem parseTlaSel_plain_flag :
    (parseTlaSelInstr (.plain "sel"
      ["(16|M0)", "(lt)f0.0", "r66.0<1>:f", "r66.0<1;1,0>:f", "acc0.0<1;1,0>:f", "{Compacted}"])).bind
      (fun s => s.flag?) = some (0, 0) := by decide

theorem parseTlaSel_outer_flag :
    (parseTlaSelInstr (.predicated "(f3.1) sel"
      ["(16|M0)", "acc0.0<1>:f", "r2.2<0;1,0>:f", "0xFF800000:f", "{Compacted}"])).bind
      (fun s => s.flag?) = some (3, 1) := by decide

/-- A true flag selects the first source. -/
theorem tlaSelStep_true (st : TlaState) (s : TlaSel) (n m : Nat)
    (hf : s.flag? = some (n, m)) (h : st.flags n m ≠ 0) (i : Nat) :
    s.value st i = readSelSrc st s.src1 i := by
  unfold TlaSel.value
  rw [hf]
  exact ite_eq_right h

/-- A clear flag selects the second source. -/
theorem tlaSelStep_false (st : TlaState) (s : TlaSel) (n m : Nat)
    (hf : s.flag? = some (n, m)) (h : st.flags n m = 0) (i : Nat) :
    s.value st i = readSelSrc st s.src2 i := by
  unfold TlaSel.value
  rw [hf]
  exact ite_eq_left h

/-- A `sel` to a GRF frames other registers. -/
theorem tlaSelStep_frame (st : TlaState) (s : TlaSel) (g : Grf)
    (hd : s.dst = .r g) (r j : Nat) (hr : r ≠ g.num) :
    (s.step st).regs r j = st.regs r j := by
  unfold TlaSel.step
  rw [hd]
  unfold writeTlaMasked
  simp [hr]

end IntelGpu
