-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.Bf16Pack
public meta import Std.Tactic.BVDecide.Reflect

@[expose] public section

/-!
# RNE FP32 -> BF16

The softmax block is converted to BF16 before the PV DPAS. `bf16Round`
implements round-to-nearest-even on the high 16 bits of an FP32 word:

* below half an ulp: keep the high half;
* above half: increment;
* exactly half: increment iff the high half is odd (ties to even).

`bf16RoundWord` packs the result back into the high half of a 32-bit word,
which is the layout the DPAS sources use. The module proves that the packed
result has zero low bits, is idempotent, and the three RNE boundary cases.
-/

namespace IntelGpu

/-- Round an FP32 word to BF16, ties to even. -/
def bf16Round (w : Word) : Bf16 :=
  let hi := (w >>> 16).truncate 16
  let lo := (w &&& 0xFFFF).truncate 16
  if BitVec.ult 0x8000 lo then hi + 1
  else if lo = 0x8000 then (if hi &&& 1 = 1 then hi + 1 else hi)
  else hi

/-- The rounded value in the packed high-half layout. -/
def bf16RoundWord (w : Word) : Word := (bf16Round w).zeroExtend 32 <<< 16

/-- The packed result has no low-half bits. -/
theorem bf16RoundWord_low_zero (w : Word) : bf16RoundWord w &&& 0xFFFF = 0 := by
  unfold bf16RoundWord
  bv_decide

/-- Rounding is idempotent. -/
theorem bf16RoundWord_idempotent (w : Word) :
    bf16RoundWord (bf16RoundWord w) = bf16RoundWord w := by
  unfold bf16RoundWord bf16Round
  bv_decide

/-- An already-packed BF16 word is unchanged. -/
theorem bf16RoundWord_packed (b : Bf16) :
    bf16RoundWord (bf16ToWord b) = bf16ToWord b := by
  unfold bf16RoundWord bf16Round bf16ToWord
  bv_decide

/-- Rounding only truncates or adds one BF16 ulp. -/
theorem bf16RoundWord_trunc_or_succ (w : Word) :
    bf16RoundWord w = (w &&& 0xFFFF0000) ∨
      bf16RoundWord w = (w &&& 0xFFFF0000) + 0x10000 := by
  unfold bf16RoundWord bf16Round
  bv_decide

/-- The round-up decision: above half, or a tie with an odd high half. -/
theorem bf16RoundWord_rounds_up (w : Word) :
    (bf16RoundWord w = (w &&& 0xFFFF0000) + 0x10000) ↔
      (BitVec.ult 0x8000 (w &&& 0xFFFF) ∨
       ((w &&& 0xFFFF) = 0x8000 ∧ ((w >>> 16) &&& 1) = 1)) := by
  unfold bf16RoundWord bf16Round
  bv_decide

/-- Tie with an even high half rounds down. -/
theorem bf16Round_tie_even_down : bf16Round 0x3F808000 = 0x3F80 := by decide

/-- Tie with an odd high half rounds up. -/
theorem bf16Round_tie_even_up : bf16Round 0x3F818000 = 0x3F82 := by decide

/-- Above half an ulp rounds up. -/
theorem bf16Round_above_half : bf16Round 0x3F80C000 = 0x3F81 := by decide

end IntelGpu
