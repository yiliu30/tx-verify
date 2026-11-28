-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaCmpCond
public import Intel.TlaSel
public import Intel.TlaSyncAllwr
public import Intel.TlaMath
public import Intel.TlaMovExec

@[expose] public section

/-!
# Bit-field and message instructions

After all other decoders, exactly six of the 2252 statements remain: four
`bfn` bit-field forms and two `send.gtwy` messages. This module decodes them
and proves that every statement in the dump is decoded by one of the parsers.

`bfn.(s0&s1|s2)` computes `(s0 &&& s1) ||| s2` per element and
`bfn.(s0|s1|s2)` computes `s0 ||| s1 ||| s2`. The send forms record the
destination, source, payload and the EOT flag (the last message carries
`EOT`).
-/

namespace IntelGpu

/-- The three printed bit-field forms. -/
inductive TlaBfnOp where
  | andOr
  | or3
  | mux
  deriving Repr, DecidableEq

structure TlaBfn where
  exec : Exec
  dst : TlaDst
  src0 : TlaSrc
  src1 : TlaSrc
  src2 : TlaSrc
  op : TlaBfnOp
  deriving Repr, DecidableEq

/-- The bfn source forms include `<v;w>` without an explicit hstride. -/
def parseBfnSrc (s : String) : Option TlaSrc :=
  match negatedReg s with
  | some g => some g
  | none =>
      match numRuns (operandCore s) with
      | [n, sub, v, w] => some (.reg ⟨n, 0, sub, v, w, 0⟩)
      | _ => parseTlaSrc s

/-- A plain `bfn.(s0&s1|s2)`, `bfn.(s0|s1|s2)` or `bfn.(s0&s1|~s0&s2)` form. -/
def parseTlaBfn : TlaInstr → Option TlaBfn
  | .plain "bfn.(s0&s1|s2)" (e :: dst :: s0 :: s1 :: s2 :: _) =>
      match parseTlaExec e, parseTlaDst dst, parseBfnSrc s0, parseBfnSrc s1,
        parseBfnSrc s2 with
      | some ex, some d, some a, some b, some c => some ⟨ex, d, a, b, c, .andOr⟩
      | _, _, _, _, _ => none
  | .plain "bfn.(s0|s1|s2)" (e :: dst :: s0 :: s1 :: s2 :: _) =>
      match parseTlaExec e, parseTlaDst dst, parseBfnSrc s0, parseBfnSrc s1,
        parseBfnSrc s2 with
      | some ex, some d, some a, some b, some c => some ⟨ex, d, a, b, c, .or3⟩
      | _, _, _, _, _ => none
  | .plain "bfn.(s0&s1|~s0&s2)" (e :: dst :: s0 :: s1 :: s2 :: _) =>
      match parseTlaExec e, parseTlaDst dst, parseBfnSrc s0, parseBfnSrc s1,
        parseBfnSrc s2 with
      | some ex, some d, some a, some b, some c => some ⟨ex, d, a, b, c, .mux⟩
      | _, _, _, _, _ => none
  | .predicated "(W) bfn.(s0&s1|~s0&s2)" (e :: dst :: s0 :: s1 :: s2 :: _) =>
      match parseTlaExec e, parseTlaDst dst, parseBfnSrc s0, parseBfnSrc s1,
        parseBfnSrc s2 with
      | some ex, some d, some a, some b, some c => some ⟨ex, d, a, b, c, .mux⟩
      | _, _, _, _, _ => none
  | _ => none

def realTlaGemmBfn : List TlaBfn :=
  (decodeTlaProgram realTlaGemm).filterMap parseTlaBfn

/-- The per-element bit-field result. -/
def TlaBfn.value (rf : RegFile) (b : TlaBfn) (l : Nat) : Word :=
  let x := readTlaSrc rf b.src0 l
  let y := readTlaSrc rf b.src1 l
  let z := readTlaSrc rf b.src2 l
  match b.op with
  | .andOr => (x &&& y) ||| z
  | .or3 => x ||| y ||| z
  | .mux => (x &&& y) ||| (~~~x &&& z)

/-- The mux form selects bits of `s1`/`s2` under the `s0` mask. -/
theorem TlaBfn.value_mux (rf : RegFile) (b : TlaBfn) (h : b.op = .mux) (l : Nat) :
    b.value rf l =
      (readTlaSrc rf b.src0 l &&& readTlaSrc rf b.src1 l) |||
        (~~~readTlaSrc rf b.src0 l &&& readTlaSrc rf b.src2 l) := by
  simp [TlaBfn.value, h]

def TlaBfn.step (rf : RegFile) (b : TlaBfn) : RegFile :=
  match b.dst with
  | .null => rf
  | .reg g => writeTlaMasked rf g b.exec (b.value rf)

set_option maxRecDepth 1000000 in
/-- There are four `bfn` forms. -/
theorem realTlaGemmBfn_length : realTlaGemmBfn.length = 4 := by decide

set_option maxRecDepth 100000 in
/-- PC 72 is the first `bfn` form. -/
theorem progInstr72 :
    progInstrAt 72 = some (.plain "bfn.(s0&s1|s2)"
      ["(16|M0)", "r62.0<1>:ud", "r16.0<1;0>:ud", "r2.3<0;0>:ud", "r2.9<0>:ud"]) := by
  decide

set_option maxRecDepth 100000 in
/-- PC 72 decodes to an `and-or` bit-field form. -/
theorem parseTlaBfn_72 :
    (progInstrAt 72).bind parseTlaBfn =
      some ⟨⟨16, 0, true⟩, .reg ⟨62, 0, 0, 1, 1, 1⟩,
        .reg ⟨16, 0, 0, 1, 0, 0⟩, .reg ⟨2, 0, 3, 0, 0, 0⟩,
        .reg ⟨2, 0, 9, 0, 1, 0⟩, .andOr⟩ := by
  decide

structure TlaSend where
  exec : Exec
  dst : String
  src : String
  payload : String
  eot : Bool
  deriving Repr, DecidableEq

/-- Does an operand start with `{EOT`? -/
def startsEot : List Char → Bool
  | '{' :: 'E' :: 'O' :: 'T' :: _ => true
  | _ => false

/-- A `send.gtwy` form. -/
def parseTlaSend : TlaInstr → Option TlaSend
  | .predicated "(W) send.gtwy" (e :: dst :: src :: _null :: payload :: rest) =>
      match parseTlaExec e with
      | some ex => some ⟨ex, dst, src, payload, rest.any (fun s => startsEot s.toList)⟩
      | none => none
  | _ => none

def realTlaGemmSend : List TlaSend :=
  (decodeTlaProgram realTlaGemm).filterMap parseTlaSend

set_option maxRecDepth 10000000 in
/-- There are two `send.gtwy` forms. -/
theorem realTlaGemmSend_length : realTlaGemmSend.length = 2 := by decide

set_option maxRecDepth 1000000 in
/-- PC 2246 is the final end-of-thread send. -/
theorem progInstr2246 :
    progInstrAt 2246 = some (.predicated "(W) send.gtwy"
      ["(1|M0)", "null", "r112", "null:0", "0x0", "0x02000010", "{EOT,F@1,$11}"]) := by
  decide

set_option maxRecDepth 1000000 in
/-- PC 2246 decodes to an EOT send. -/
theorem parseTlaSend_2246 :
    (progInstrAt 2246).bind parseTlaSend =
      some ⟨⟨1, 0, true⟩, "null", "r112", "0x0", true⟩ := by
  decide

set_option maxRecDepth 10000000 in
/-- One of the two sends is an EOT. -/
theorem realTlaGemmSend_eot :
    (realTlaGemmSend.filter (fun s => s.eot)).length = 1 := by
  decide

/-- Every statement of the dump is decoded by one of the parsers. -/
def decodedAll (i : TlaInstr) : Bool :=
  match i with
  | .label _ => true
  | .dpas _ _ _ _ _ _ => true
  | _ =>
    (parseTlaMovInstr i).isSome || (parseTlaMovPlain i).isSome ||
    (parseTlaAluInstr i).isSome || (parseTlaAluPlain i).isSome ||
    (parseTlaBlock2dInstr i).isSome || (parseTlaBlock2dPlain i).isSome ||
    (parseTlaBlock2dPlainStore i).isSome ||
    (parseTlaCmpInstr i).isSome || (parseTlaSelInstr i).isSome ||
    (parseTlaSyncAllwr i).isSome || (parseTlaMath i).isSome ||
    (parseTlaJmpInstr i).isSome ||
    (parseTlaBfn i).isSome || (parseTlaSend i).isSome ||
    (match i with
     | .plain "sync.nop" _ => true
     | .plain "sync.allrd" _ => true
     | .predicated "(W) sync.bar" _ => true
     | .plain "join" _ => true
     | _ => false)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
/-- All 2252 statements are decoded. -/
theorem realTlaGemm_decoded_all :
    withPc.all (fun p => decodedAll p.2) = true := by
  decide

end IntelGpu
