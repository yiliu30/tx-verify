-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.SendSbid

@[expose] public section

/-!
# SBID fields in an encoded SEND descriptor

`Intel.SendSbid` models the SEND scoreboard with an abstract `Token := Nat`.
The binary dumps used in this development do not print the SBID field, so the
mapping from a descriptor word to a token was left as an assumption (the
SEND/SBID row in `Intel/REVIEW_63.md`). This module makes one concrete,
auditable transcription of that mapping and proves the token plumbing used by
the SEND model.

## Assumed descriptor layout

This is a model assumption, not a hardware-conformance claim. A `SendDesc` is
a 32-bit `Word` with this field layout:

- bits `[0, 8)`: reserved in this model;
- bits `[8, 16)`: SBID, an 8-bit unsigned field;
- bits `[16, 32)`: reserved in this model.

`mkDesc` constructs the canonical descriptor for an SBID by zeroing both
reserved ranges. `sbidOf` extracts bits `[8, 16)` with a right shift and an
eight-bit mask, i.e. `(w >>> 8) &&& 0xff`. The encoding is transcribed into
this model; it is not read from the dumps.

The field is eight bits wide, but the modeled scoreboard has only eight SBID
tokens (`0..7`, three bits). That narrower token set is also a model
assumption. It keeps the token set finite and makes the out-of-range case
explicit: descriptors whose extracted SBID is at least eight are rejected by
`issueLoadSbid` / `issueStoreSbid`, leaving the state unchanged.

## What is proved

- `sbidOf_lt`: every extracted field fits in the eight-bit field width.
- `sbidOf_mk`: `mkDesc` round-trips through `sbidOf` for every in-field SBID.
- `tokenOfDesc_mk` / `distinct_sbids_distinct_tokens`: valid distinct SBIDs
  map to distinct tokens.
- `issueLoadSbid_pair_pending` / `issueStoreSbid_pair_pending`: two SENDs
  with distinct SBIDs leave both tokens pending.
- `issueLoadSbid_pair_allDone_progression` and the store version: the pair is
  not `allDone` after issue or after only one completion, and is `allDone`
  after both complete.
- `waitSbid_done_other`, `commitLoadSbid_other_pending` and
  `wait_commitLoad_other_stalls`: waiting on or committing one token does not
  consume the other.
- `loadPipelineSbid_wait` / `loadPipelineSbid_value`: issue, wait and commit
  of an encoded load descriptor succeeds on the same SBID and writes the
  sampled memory value, reusing `Intel.SendSbid`'s pipeline facts.
- `issueLoadSbid_outOfRange`: an out-of-range SBID field is rejected.
-/

namespace IntelGpu

/-- A transcribed 32-bit SEND descriptor. The dumps do not print SBIDs, so
this layout is a model assumption; see the module docstring. -/
abbrev SendDesc := Word

/-- Low bit of the assumed SBID field: bits `[8, 16)` carry the SBID. -/
def sbidShift : Nat := 8
/-- Width of the assumed SBID field, in bits. -/
def sbidWidth : Nat := 8
/-- An eight-bit mask, applied after shifting the field down. -/
def sbidMask : Word := BitVec.ofNat 32 (2 ^ sbidWidth - 1)

/-- Extract the assumed SBID field from bits `[8, 16)`; this is
`(w >>> 8) &&& 0xff` after the definitions unfold. -/
def sbidOf (w : SendDesc) : Nat := ((w >>> sbidShift) &&& sbidMask).toNat

/-- Canonical descriptor: `sbid` in bits `[8, 16)`, reserved bits zero. -/
def mkDesc (sbid : Nat) : SendDesc := (BitVec.ofNat 32 sbid) <<< sbidShift


/-- The bits of `2 ^ n - 1` are set exactly below `n`.

This local proof avoids the core `Nat.testBit_two_pow_sub_one` lemma, whose
proof depends on `Classical.choice` in the current toolchain. -/
theorem testBit_two_pow_sub_one_choiceFree (n i : Nat) :
    Nat.testBit (2 ^ n - 1) i = decide (i < n) := by
  induction n generalizing i with
  | zero =>
      cases i <;> simp
  | succ n ih =>
      cases i with
      | zero =>
          rw [Nat.testBit_zero]
          have hmod : (2 ^ (n + 1) - 1) % 2 = 1 := by
            rw [Nat.pow_succ]
            have hp : 0 < 2 ^ n := Nat.two_pow_pos _
            omega
          simp [hmod]
      | succ j =>
          rw [Nat.testBit_succ]
          have hdiv : (2 ^ (n + 1) - 1) / 2 = 2 ^ n - 1 := by
            rw [Nat.pow_succ]
            have hp : 0 < 2 ^ n := Nat.two_pow_pos _
            omega
          rw [hdiv, ih j]
          simp

/-- Masking by `2 ^ n - 1` is reduction modulo `2 ^ n`. -/
theorem and_two_pow_sub_one_eq_mod_choiceFree (x n : Nat) :
    x &&& (2 ^ n - 1) = x % 2 ^ n := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_mod_two_pow,
    testBit_two_pow_sub_one_choiceFree]
  simp [Bool.and_comm]

/-- A value below `2 ^ n` is unchanged by the `2 ^ n - 1` mask. -/
theorem and_mask_eq_self (n x : Nat) (h : x < 2 ^ n) :
    x &&& (2 ^ n - 1) = x := by
  rw [and_two_pow_sub_one_eq_mod_choiceFree, Nat.mod_eq_of_lt h]

/-- The mask's numeric value is the field-width mask. -/
theorem sbidMask_toNat : sbidMask.toNat = 2 ^ sbidWidth - 1 := by
  unfold sbidMask sbidWidth
  rw [BitVec.toNat_ofNat]

/-- Every extracted SBID fits in the declared field width. -/
theorem sbidOf_lt (w : SendDesc) : sbidOf w < 2 ^ sbidWidth := by
  unfold sbidOf
  rw [BitVec.toNat_and, sbidMask_toNat]
  apply Nat.and_lt_two_pow
  have hp : 0 < 2 ^ sbidWidth := Nat.two_pow_pos _
  omega

/-- `mkDesc` round-trips through `sbidOf` for every in-field SBID. -/
theorem sbidOf_mk (sbid : Nat) (h : sbid < 2 ^ sbidWidth) :
    sbidOf (mkDesc sbid) = sbid := by
  delta sbidOf mkDesc sbidShift sbidWidth sbidMask
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  simp only [Nat.reducePow, Nat.reduceMod, Nat.reduceSub]
  rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have h8 : sbid < 2 ^ 8 := by simpa [sbidWidth] using h
  have hs : sbid % 2 ^ 32 = sbid := by
    apply Nat.mod_eq_of_lt
    omega
  have hm : sbid * 2 ^ 8 % 2 ^ 32 = sbid * 2 ^ 8 := by
    apply Nat.mod_eq_of_lt
    omega
  rw [hs, hm, Nat.mul_div_cancel sbid (by decide : 0 < 2 ^ 8)]
  exact and_mask_eq_self 8 sbid h8

/-- Width of the modeled legal SBID token set. The descriptor field is eight
bits wide; only these low three bits name legal scoreboard tokens here. -/
def sbidTokenBits : Nat := 3

/-- Whether `t` is in the modeled legal SBID token set. -/
def tokenValid (t : Token) : Bool := decide (t < 2 ^ sbidTokenBits)

/-- The token named by a descriptor's SBID field. -/
def tokenOfDesc (d : SendDesc) : Token := sbidOf d

/-- The token of a canonical descriptor is its encoded SBID. -/
theorem tokenOfDesc_mk (sbid : Nat) (h : sbid < 2 ^ sbidWidth) :
    tokenOfDesc (mkDesc sbid) = sbid := by
  simpa [tokenOfDesc] using sbidOf_mk sbid h

/-- Distinct valid SBIDs give distinct tokens, hence no token reuse. -/
theorem distinct_sbids_distinct_tokens {sbid1 sbid2 : Nat}
    (h1 : sbid1 < 2 ^ sbidWidth) (h2 : sbid2 < 2 ^ sbidWidth)
    (hne : sbid1 ≠ sbid2) :
    tokenOfDesc (mkDesc sbid1) ≠ tokenOfDesc (mkDesc sbid2) := by
  rw [tokenOfDesc_mk sbid1 h1, tokenOfDesc_mk sbid2 h2]
  exact hne

/-- Issue a load on the token encoded in `d`. The state's `next` counter is
aligned with the descriptor's SBID so the existing `issueLoad` records that
token. Out-of-range SBIDs are rejected. -/
def issueLoadSbid (s : SendState) (d : SendDesc) (reg addr : Nat) : SendState :=
  if tokenValid (sbidOf d) then
    issueLoad { s with next := sbidOf d } reg addr
  else s

/-- Issue a store on the token encoded in `d`; out-of-range SBIDs are
rejected. -/
def issueStoreSbid (s : SendState) (d : SendDesc) (addr : Nat)
    (val : Word) : SendState :=
  if tokenValid (sbidOf d) then
    issueStore { s with next := sbidOf d } addr val
  else s

/-- Legal modeled SBIDs satisfy `tokenValid`. -/
theorem tokenValid_true {t : Token} (h : t < 2 ^ sbidTokenBits) :
    tokenValid t = true := by
  simp [tokenValid, h]

/-- SBIDs outside the modeled token set are invalid. -/
theorem tokenValid_false {t : Token} (h : 2 ^ sbidTokenBits ≤ t) :
    tokenValid t = false := by
  simp [tokenValid, Nat.not_lt.mpr h]

/-- A valid encoded load leaves its own SBID token pending. -/
theorem issueLoadSbid_pending (s : SendState) (d : SendDesc) (reg addr : Nat)
    (h : tokenValid (sbidOf d) = true) :
    (issueLoadSbid s d reg addr).status (sbidOf d) = .pending := by
  simp [issueLoadSbid, h, issueLoad]

/-- A valid encoded store leaves its own SBID token pending. -/
theorem issueStoreSbid_pending (s : SendState) (d : SendDesc) (addr : Nat)
    (val : Word) (h : tokenValid (sbidOf d) = true) :
    (issueStoreSbid s d addr val).status (sbidOf d) = .pending := by
  simp [issueStoreSbid, h, issueStore]

/-- Two loads with distinct encoded SBIDs stay pending together. -/
theorem issueLoadSbid_pair_pending (s : SendState) (d1 d2 : SendDesc)
    (reg1 addr1 reg2 addr2 : Nat)
    (h1 : tokenValid (sbidOf d1) = true)
    (h2 : tokenValid (sbidOf d2) = true)
    (hne : sbidOf d1 ≠ sbidOf d2) :
    let s1 := issueLoadSbid s d1 reg1 addr1
    let s2 := issueLoadSbid s1 d2 reg2 addr2
    s2.status (sbidOf d1) = .pending ∧ s2.status (sbidOf d2) = .pending := by
  dsimp only
  constructor
  · simp [issueLoadSbid, h1, h2, issueLoad, hne]
  · simp [issueLoadSbid, h2, issueLoad]

/-- Two stores with distinct encoded SBIDs stay pending together. -/
theorem issueStoreSbid_pair_pending (s : SendState) (d1 d2 : SendDesc)
    (addr1 addr2 : Nat) (val1 val2 : Word)
    (h1 : tokenValid (sbidOf d1) = true)
    (h2 : tokenValid (sbidOf d2) = true)
    (hne : sbidOf d1 ≠ sbidOf d2) :
    let s1 := issueStoreSbid s d1 addr1 val1
    let s2 := issueStoreSbid s1 d2 addr2 val2
    s2.status (sbidOf d1) = .pending ∧ s2.status (sbidOf d2) = .pending := by
  dsimp only
  constructor
  · simp [issueStoreSbid, h1, h2, issueStore, hne]
  · simp [issueStoreSbid, h2, issueStore]

/-- A pending first token prevents `allDone` for a pair. -/
theorem allDone_pair_false_left (s : SendState) (t1 t2 : Token)
    (h : s.status t1 = .pending) : allDone s [t1, t2] = false := by
  simp [allDone, h]

/-- A pending second token prevents `allDone` for a pair. -/
theorem allDone_pair_false_right (s : SendState) (t1 t2 : Token)
    (h : s.status t2 = .pending) : allDone s [t1, t2] = false := by
  simp [allDone, h]

/-- A pair is `allDone` exactly when both tokens are done. -/
theorem allDone_pair_true (s : SendState) (t1 t2 : Token) :
    allDone s [t1, t2] = true ↔ s.status t1 = .done ∧ s.status t2 = .done := by
  simp [allDone]

/-- Completing one token leaves another token's status unchanged. -/
theorem status_complete_other (s : SendState) (t1 t2 : Token)
    (hne : t2 ≠ t1) : (complete s t1).status t2 = s.status t2 := by
  unfold complete
  split
  · simp [hne]
  · rfl

/-- Committing a load leaves every token's status unchanged. -/
theorem status_commitLoad_other (s : SendState) (t1 t2 : Token) (reg : Nat) :
    (commitLoad s t1 reg).status t2 = s.status t2 := by
  unfold commitLoad
  split <;> simp

/-- Completion of one token does not consume another pending token. -/
theorem complete_other_pending (s : SendState) (t1 t2 : Token)
    (hne : t2 ≠ t1) (h : s.status t2 = .pending) :
    (complete s t1).status t2 = .pending := by
  rw [status_complete_other s t1 t2 hne, h]

/-- Committing one load does not consume another pending token. -/
theorem commitLoad_other_pending (s : SendState) (t1 t2 : Token) (reg : Nat)
    (h : s.status t2 = .pending) :
    (commitLoad s t1 reg).status t2 = .pending := by
  rw [status_commitLoad_other, h]

/-- After committing one load, waiting on another pending token still
stalls. -/
theorem wait_commitLoad_other_stalls (s : SendState) (t1 t2 : Token) (reg : Nat)
    (h : s.status t2 = .pending) :
    wait (commitLoad s t1 reg) t2 = none := by
  apply wait_pending
  rw [status_commitLoad_other, h]

/-- A canonical descriptor whose field is outside the modeled token set is
invalid. -/
theorem mkDesc_outOfRange (sbid : Nat)
    (hlo : 2 ^ sbidTokenBits ≤ sbid) (hhi : sbid < 2 ^ sbidWidth) :
    tokenValid (sbidOf (mkDesc sbid)) = false := by
  rw [sbidOf_mk sbid hhi]
  exact tokenValid_false hlo


/-- An `allDone` pair requires both tokens, so one pending token suffices
to make it false. -/
theorem allDone_pair_false_until_both (s : SendState) (t1 t2 : Token)
    (h : s.status t1 = .pending ∨ s.status t2 = .pending) :
    allDone s [t1, t2] = false := by
  rcases h with h | h
  · exact allDone_pair_false_left s t1 t2 h
  · exact allDone_pair_false_right s t1 t2 h

/-- Completing two distinct pending tokens makes both done. -/
theorem complete_pair_done (s : SendState) (t1 t2 : Token)
    (hne : t1 ≠ t2) (h1 : s.status t1 = .pending)
    (h2 : s.status t2 = .pending) :
    (complete (complete s t1) t2).status t1 = .done ∧
      (complete (complete s t1) t2).status t2 = .done := by
  constructor
  · rw [status_complete_other (complete s t1) t2 t1 hne]
    exact complete_pending s t1 h1
  · apply complete_pending
    exact complete_other_pending s t1 t2 (Ne.symm hne) h2

/-- `allDone` progression for two encoded load SENDs: false after issue,
false after one completion, true after both. -/
theorem issueLoadSbid_pair_allDone_progression (s : SendState)
    (d1 d2 : SendDesc) (reg1 addr1 reg2 addr2 : Nat)
    (h1 : tokenValid (sbidOf d1) = true)
    (h2 : tokenValid (sbidOf d2) = true)
    (hne : sbidOf d1 ≠ sbidOf d2) :
    let s1 := issueLoadSbid s d1 reg1 addr1
    let s2 := issueLoadSbid s1 d2 reg2 addr2
    allDone s2 [sbidOf d1, sbidOf d2] = false ∧
      allDone (complete s2 (sbidOf d1)) [sbidOf d1, sbidOf d2] = false ∧
      allDone (complete (complete s2 (sbidOf d1)) (sbidOf d2))
        [sbidOf d1, sbidOf d2] = true := by
  dsimp only
  obtain ⟨hp1, hp2⟩ :=
    issueLoadSbid_pair_pending s d1 d2 reg1 addr1 reg2 addr2 h1 h2 hne
  refine ⟨?_, ?_, ?_⟩
  · exact allDone_pair_false_until_both _ _ _ (Or.inl hp1)
  · apply allDone_pair_false_until_both
    exact Or.inr (complete_other_pending _ _ _ (Ne.symm hne) hp2)
  · rw [allDone_pair_true]
    exact complete_pair_done _ _ _ hne hp1 hp2

/-- `allDone` progression for two encoded store SENDs: false after issue,
false after one completion, true after both. -/
theorem issueStoreSbid_pair_allDone_progression (s : SendState)
    (d1 d2 : SendDesc) (addr1 addr2 : Nat) (val1 val2 : Word)
    (h1 : tokenValid (sbidOf d1) = true)
    (h2 : tokenValid (sbidOf d2) = true)
    (hne : sbidOf d1 ≠ sbidOf d2) :
    let s1 := issueStoreSbid s d1 addr1 val1
    let s2 := issueStoreSbid s1 d2 addr2 val2
    allDone s2 [sbidOf d1, sbidOf d2] = false ∧
      allDone (complete s2 (sbidOf d1)) [sbidOf d1, sbidOf d2] = false ∧
      allDone (complete (complete s2 (sbidOf d1)) (sbidOf d2))
        [sbidOf d1, sbidOf d2] = true := by
  dsimp only
  obtain ⟨hp1, hp2⟩ :=
    issueStoreSbid_pair_pending s d1 d2 addr1 addr2 val1 val2 h1 h2 hne
  refine ⟨?_, ?_, ?_⟩
  · exact allDone_pair_false_until_both _ _ _ (Or.inl hp1)
  · apply allDone_pair_false_until_both
    exact Or.inr (complete_other_pending _ _ _ (Ne.symm hne) hp2)
  · rw [allDone_pair_true]
    exact complete_pair_done _ _ _ hne hp1 hp2

/-- Committing one encoded load leaves another SBID token pending. -/
theorem commitLoadSbid_other_pending (s : SendState) (d1 d2 : SendDesc)
    (reg : Nat) (h : s.status (tokenOfDesc d2) = .pending) :
    (commitLoad s (tokenOfDesc d1) reg).status (tokenOfDesc d2) = .pending := by
  rw [status_commitLoad_other, h]

/-- Waiting on a done token returns the same state, so another token's
status is untouched. -/
theorem waitSbid_done_other (s : SendState) (d1 d2 : SendDesc)
    (h : s.status (tokenOfDesc d1) = .done) :
    ∃ s', wait s (tokenOfDesc d1) = some s' ∧
      s'.status (tokenOfDesc d2) = s.status (tokenOfDesc d2) := by
  exact ⟨s, wait_done s _ h, rfl⟩

/-- An invalid encoded load issue is rejected and changes nothing. -/
theorem issueLoadSbid_rejects (s : SendState) (d : SendDesc) (reg addr : Nat)
    (h : tokenValid (sbidOf d) = false) :
    issueLoadSbid s d reg addr = s := by
  simp [issueLoadSbid, h]

/-- An invalid encoded store issue is rejected and changes nothing. -/
theorem issueStoreSbid_rejects (s : SendState) (d : SendDesc) (addr : Nat)
    (val : Word) (h : tokenValid (sbidOf d) = false) :
    issueStoreSbid s d addr val = s := by
  simp [issueStoreSbid, h]

/-- Negative robustness fact: a descriptor whose SBID field is outside the
modeled token set is rejected by `issueLoadSbid`. -/
theorem issueLoadSbid_outOfRange (s : SendState) (sbid reg addr : Nat)
    (hlo : 2 ^ sbidTokenBits ≤ sbid) (hhi : sbid < 2 ^ sbidWidth) :
    issueLoadSbid s (mkDesc sbid) reg addr = s := by
  exact issueLoadSbid_rejects s (mkDesc sbid) reg addr (mkDesc_outOfRange sbid hlo hhi)

/-- Issue, complete and commit an encoded load, using the SBID as the
token throughout. -/
def loadPipelineSbid (s : SendState) (d : SendDesc) (reg addr : Nat) : SendState :=
  let t := tokenOfDesc d
  let s1 := issueLoadSbid s d reg addr
  let s2 := complete s1 t
  commitLoad s2 t reg

/-- After completion, `wait` on the encoded load's own SBID succeeds and
returns the same state. -/
theorem loadPipelineSbid_wait (s : SendState) (d : SendDesc) (reg addr : Nat)
    (h : tokenValid (sbidOf d) = true) :
    wait (complete (issueLoadSbid s d reg addr) (tokenOfDesc d)) (tokenOfDesc d) =
      some (complete (issueLoadSbid s d reg addr) (tokenOfDesc d)) := by
  apply wait_done
  apply complete_pending
  exact issueLoadSbid_pending s d reg addr h

/-- The encoded load pipeline writes the value sampled at issue to the
destination register. -/
theorem loadPipelineSbid_value (s : SendState) (d : SendDesc) (reg addr : Nat)
    (h : tokenValid (sbidOf d) = true) :
    (loadPipelineSbid s d reg addr).regs reg = s.mem addr := by
  unfold loadPipelineSbid
  simp [tokenOfDesc, issueLoadSbid, h, issueLoad, complete, commitLoad]

end IntelGpu
