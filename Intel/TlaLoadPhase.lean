-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaAccumulatorStore
public import Intel.TlaBlock2dPlain

@[expose] public section

/-!
# The block2d load/store phase of the mainloop

The mainloop block contains 137 block2d instructions: the 130 predicated
`load.ugm`/`store.ugm` forms and the 7 plain `load_block2d.ugm` forms. This
module executes them in program order over the register-window semantics,
treating the six `null:0` operands as no-ops.

The load/store phase does not touch any register element at index 8 or above:
a window only spans elements 0..7. In particular the loop counters `r1.11`,
`r1.14` and the bound `r1.15` are preserved, so the phase can be inserted
around the DPAS phase without disturbing the loop tail.
-/

namespace IntelGpu

/-- A predicated or plain block2d load. -/
def TlaBlock2d.isLoadAny (b : TlaBlock2d) : Bool :=
  b.isLoad || isPlainB2dOp b.opcode

/-- Execute one block2d instruction over the window semantics. `null:0`
operands are modelled as no-ops. -/
def TlaBlock2d.loadStoreStep (st : TlaState) (m : TlaMem) (bti : Nat → Word)
    (b : TlaBlock2d) : Option (TlaState × TlaMem) :=
  match b.window? with
  | none => some (st, m)
  | some w =>
      if b.isLoadAny then tlaBlock2dLoadW? st m bti w b
      else tlaBlock2dStoreW? st m bti w b

/-- No window covers an element at index 8 or above. -/
theorem TlaWindow.index_of_ge8 (w : TlaWindow) (r j : Nat) (hj : 8 ≤ j) :
    w.index r j = none := by
  apply TlaWindow.index_none
  intro h
  exact absurd h.2.2 (by omega)

theorem loadStoreStep_preserves_high (st : TlaState) (m : TlaMem) (bti : Nat → Word)
    (b : TlaBlock2d) (st' : TlaState) (m' : TlaMem)
    (h : TlaBlock2d.loadStoreStep st m bti b = some (st', m'))
    (r j : Nat) (hj : 8 ≤ j) :
    st'.regs r j = st.regs r j := by
  unfold TlaBlock2d.loadStoreStep at h
  cases hw : b.window? with
  | none =>
      simp only [hw, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
  | some w =>
      by_cases hl : b.isLoadAny = true
      · simp only [hw, hl, if_pos] at h
        exact tlaBlock2dLoadW?_frame st m bti w b (st', m') h r j
          (TlaWindow.index_of_ge8 w r j hj)
      · have hl' : b.isLoadAny = false := by simpa using hl
        simp only [hw, hl', Bool.false_eq_true, if_false] at h
        have hregs : st' = st := tlaBlock2dStoreW?_regs st m bti w b (st', m') h
        rw [hregs]

/-- The block's block2d instructions with their program counters. -/
def blockB2d : List (Nat × TlaBlock2d) :=
  blockInstrs.filterMap (fun p =>
    match parseTlaBlock2dInstr p.2 with
    | some b => some (p.1, b)
    | none => (parseTlaBlock2dPlain p.2).map (fun b => (p.1, b)))

def blockLoadPhaseStep (bti : Nat → Word) (acc : Option (TlaState × TlaMem))
    (p : Nat × TlaBlock2d) : Option (TlaState × TlaMem) :=
  acc.bind (fun (st, m) => TlaBlock2d.loadStoreStep st m bti p.2)

/-- The block2d phase of the mainloop, in program order. -/
def blockLoadPhase (st : TlaState) (m : TlaMem) (bti : Nat → Word) :
    Option (TlaState × TlaMem) :=
  blockB2d.foldl (blockLoadPhaseStep bti) (some (st, m))

theorem blockLoadPhase_preserves_high (st : TlaState) (m : TlaMem)
    (bti : Nat → Word) (st' : TlaState) (m' : TlaMem)
    (h : blockLoadPhase st m bti = some (st', m')) (r j : Nat) (hj : 8 ≤ j) :
    st'.regs r j = st.regs r j := by
  have hnone : ∀ (l : List (Nat × TlaBlock2d)),
      List.foldl (blockLoadPhaseStep bti) none l = none := by
    intro l
    induction l with
    | nil => rfl
    | cons q qs ih =>
        rw [List.foldl_cons]
        simp [blockLoadPhaseStep, ih]
  have hfold : ∀ (l : List (Nat × TlaBlock2d)) (init : TlaState × TlaMem)
      (st' : TlaState) (m' : TlaMem),
      l.foldl (blockLoadPhaseStep bti) (some init) = some (st', m') →
      st'.regs r j = init.1.regs r j := by
    intro l
    induction l with
    | nil =>
        intro init st' m' h
        simp at h
        cases h
        rfl
    | cons p ps ih =>
        intro init st' m' h
        rw [List.foldl_cons] at h
        cases hstep : blockLoadPhaseStep bti (some init) p with
        | none =>
            rw [hstep, hnone ps] at h
            simp at h
        | some pair =>
            obtain ⟨st1, m1⟩ := pair
            have hstep' : TlaBlock2d.loadStoreStep init.1 init.2 bti p.2 = some (st1, m1) := by
              simpa [blockLoadPhaseStep] using hstep
            have h1 := loadStoreStep_preserves_high init.1 init.2 bti p.2 st1 m1 hstep' r j hj
            have h2 := ih (st1, m1) st' m' (by simpa [hstep] using h)
            rw [h2, h1]
  exact hfold blockB2d (st, m) st' m' h

/-- The load/store phase preserves the loop counters and the bound. -/
theorem blockLoadPhase_preserves_counters (st : TlaState) (m : TlaMem)
    (bti : Nat → Word) (st' : TlaState) (m' : TlaMem)
    (h : blockLoadPhase st m bti = some (st', m')) :
    st'.regs 1 11 = st.regs 1 11 ∧ st'.regs 1 14 = st.regs 1 14 ∧
      st'.regs 1 15 = st.regs 1 15 :=
  ⟨blockLoadPhase_preserves_high st m bti st' m' h 1 11 (by decide),
   blockLoadPhase_preserves_high st m bti st' m' h 1 14 (by decide),
   blockLoadPhase_preserves_high st m bti st' m' h 1 15 (by decide)⟩

set_option maxRecDepth 1000000 in
/-- The block has 137 block2d instructions. -/
theorem blockB2dPc_length : blockB2d.length = 137 := by decide

set_option maxRecDepth 1000000 in
/-- Every block2d address in the block parses. -/
theorem blockB2d_addr_parse :
    blockB2d.all (fun p => (parseTlaAddr p.2.addr).isSome) = true := by decide

/-- The load/store phase always succeeds. -/
theorem blockLoadPhase_isSome (st : TlaState) (m : TlaMem) (bti : Nat → Word) :
    (blockLoadPhase st m bti).isSome = true := by
  have hparse := blockB2d_addr_parse
  rw [List.all_eq_true] at hparse
  have hfold : ∀ (l : List (Nat × TlaBlock2d)) (init : TlaState × TlaMem),
      (∀ p ∈ l, (parseTlaAddr p.2.addr).isSome = true) →
      (l.foldl (blockLoadPhaseStep bti) (some init)).isSome = true := by
    intro l
    induction l with
    | nil => intro init _; rfl
    | cons p ps ih =>
        intro init hl
        have hp : (parseTlaAddr p.2.addr).isSome = true := hl p (by simp)
        have hstep : ∃ pair, blockLoadPhaseStep bti (some init) p = some pair := by
          unfold blockLoadPhaseStep
          simp only [Option.bind_some]
          unfold TlaBlock2d.loadStoreStep
          cases hw : p.2.window? with
          | none => exact ⟨_, rfl⟩
          | some w =>
              by_cases hl' : p.2.isLoadAny = true
              · simp only [hw, hl']
                unfold tlaBlock2dLoadW?
                cases ha : parseTlaAddr p.2.addr with
                | none => simp [ha] at hp
                | some a => exact ⟨_, rfl⟩
              · have hl'' : p.2.isLoadAny = false := by simpa using hl'
                simp only [hw, hl'', Bool.false_eq_true, if_false]
                unfold tlaBlock2dStoreW?
                cases ha : parseTlaAddr p.2.addr with
                | none => simp [ha] at hp
                | some a => exact ⟨_, rfl⟩
        obtain ⟨pair, hpair⟩ := hstep
        rw [List.foldl_cons, hpair]
        exact ih pair (by
          intro q hq
          exact hl q (by simp [hq]))
  exact hfold blockB2d (st, m) (fun p hp => hparse p hp)

end IntelGpu
