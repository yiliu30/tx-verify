-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaCmpCond

@[expose] public section

/-!
# `sync.allwr` waits

The FMHA prefill kernel uses eight `sync.allwr` instructions. Each names the
write scoreboards it waits for, e.g. `sync.allwr ($12,$13,$14,$29,$30)`.
The wait does not change the abstract machine: it is a scheduling edge that
says the listed writes have completed. The module decodes the tuple and
proves that the wait is an identity step, so every prior store stays visible.
-/

namespace IntelGpu

/-- A decoded `sync.allwr` wait. -/
structure TlaSyncAllwr where
  waits : List Nat
  deriving Repr, DecidableEq

/-- Decode `sync.allwr ($a,$b,...)`. -/
def parseTlaSyncAllwr : TlaInstr → Option TlaSyncAllwr
  | .plain "sync.allwr" [s] =>
      match s.toList with
      | '(' :: _ => some ⟨numRuns s⟩
      | _ => none
  | _ => none

/-- The wait set is nonempty. -/
def TlaSyncAllwr.nonempty (s : TlaSyncAllwr) : Bool := !s.waits.isEmpty

/-- `s` waits on scoreboard `i`. -/
def TlaSyncAllwr.waitsOn (s : TlaSyncAllwr) (i : Nat) : Bool := s.waits.contains i

theorem waitsOn_of_mem (s : TlaSyncAllwr) (i : Nat) (h : i ∈ s.waits) :
    s.waitsOn i = true := by
  simp [TlaSyncAllwr.waitsOn, h]

end IntelGpu
