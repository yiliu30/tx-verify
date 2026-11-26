-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.Asm

@[expose] public section

/-!
# SEND, SBID and the register scoreboard

The real kernels use `lsc_load.ugm` and `lsc_store.ugm`, which are SEND
messages: each issue carries a token (an SBID) and completes asynchronously.
The assembly text does not print the SBID, so this module models the mechanism
explicitly rather than reading it from the dump:

- `issueLoad` / `issueStore` assign a fresh token and mark it pending; the load
  samples memory at issue and the store captures its value.
- `complete` marks a token done; `wait` succeeds only on a done token.
- `commitLoad` writes a completed load's sampled value to its destination
  register; `commitStore` writes a completed store's value to memory.
- `loadPipeline` / `storePipeline` / `addOnePipeline` are the small
  load-add-store shape the real add-one kernel uses.

## ISA-guaranteed versus assumed

Guaranteed by the model's SEND contract and proved here:

- a fresh issue is pending (`issueLoad_pending`, `issueStore_pending`);
- `wait` blocks while a token is pending and returns the state once done
  (`wait_pending`, `wait_done`);
- committing a done load yields the sampled value, and committing a done store
  yields its captured value (`commitLoad_value`, `commitStore_value`).

Assumed, not derived from the printed assembly:

- that every issued token eventually completes (fair completion);
- that a load samples memory at issue and a store at commit;
- that the register scoreboard waits for the load before the dependent read
  (the SBID is not printed, so this is an ABI/ISA assumption here);
- that no token is reused while pending.

These assumptions are listed in `SendAssumptions` and in the README ledger.
-/

namespace IntelGpu

abbrev Token := Nat

inductive SendKind where
  | load
  | store
  deriving Repr, DecidableEq

inductive SendStatus where
  | pending
  | done
  deriving Repr, DecidableEq

structure SendState where
  mem : Nat → Word
  regs : Nat → Word
  result : Token → Word
  status : Token → SendStatus
  next : Token
  retired : List (SendKind × Token)

def issueLoad (s : SendState) (_reg addr : Nat) : SendState :=
  { s with
    result := fun t => if t = s.next then s.mem addr else s.result t,
    status := fun t => if t = s.next then .pending else s.status t,
    next := s.next + 1 }

def issueStore (s : SendState) (_addr : Nat) (val : Word) : SendState :=
  { s with
    result := fun t => if t = s.next then val else s.result t,
    status := fun t => if t = s.next then .pending else s.status t,
    next := s.next + 1 }

def complete (s : SendState) (t : Token) : SendState :=
  if s.status t = .pending then
    { s with status := fun t' => if t' = t then .done else s.status t' }
  else s

def wait (s : SendState) (t : Token) : Option SendState :=
  match s.status t with
  | .pending => none
  | .done => some s

def commitLoad (s : SendState) (t : Token) (reg : Nat) : SendState :=
  if s.status t = .done then
    { s with
      regs := fun r => if r = reg then s.result t else s.regs r,
      retired := (SendKind.load, t) :: s.retired }
  else s

def commitStore (s : SendState) (t : Token) (addr : Nat) : SendState :=
  if s.status t = .done then
    { s with
      mem := fun a => if a = addr then s.result t else s.mem a,
      retired := (SendKind.store, t) :: s.retired }
  else s

def allDone (s : SendState) (tokens : List Token) : Bool :=
  tokens.all (fun t => s.status t == .done)

/-- A load issues, completes, and commits its sampled value. -/
def loadPipeline (s : SendState) (reg addr : Nat) : SendState :=
  let t := s.next
  let s1 := issueLoad s reg addr
  let s2 := complete s1 t
  commitLoad s2 t reg

/-- A store issues, completes, and commits its captured value. -/
def storePipeline (s : SendState) (addr : Nat) (val : Word) : SendState :=
  let t := s.next
  let s1 := issueStore s addr val
  let s2 := complete s1 t
  commitStore s2 t addr

/-- The real add-one shape: load, add one, store. -/
def addOnePipeline (s : SendState) (addr reg tmp : Nat) : SendState :=
  let s1 := loadPipeline s reg addr
  let s2 := { s1 with regs := fun r => if r = tmp then s1.regs reg + 1 else s1.regs r }
  storePipeline s2 addr (s2.regs tmp)

/-- The assumed part of the SEND contract. The proved part is the lemmas below. -/
structure SendAssumptions : Prop where
  /-- Every issued token eventually completes. -/
  fairCompletion : True
  /-- A load samples memory at issue; a store captures its value at issue. -/
  sampleAtIssue : True
  /-- The register scoreboard waits for the load before the dependent read. -/
  registerScoreboard : True
  /-- No token is reused while pending. -/
  noTokenReuse : True

theorem issueLoad_pending (s : SendState) (reg addr : Nat) :
    (issueLoad s reg addr).status s.next = .pending := by
  simp [issueLoad]

theorem issueStore_pending (s : SendState) (addr : Nat) (val : Word) :
    (issueStore s addr val).status s.next = .pending := by
  simp [issueStore]

theorem complete_pending (s : SendState) (t : Token) (h : s.status t = .pending) :
    (complete s t).status t = .done := by
  simp [complete, h]

theorem wait_pending (s : SendState) (t : Token) (h : s.status t = .pending) :
    wait s t = none := by
  simp [wait, h]

theorem wait_done (s : SendState) (t : Token) (h : s.status t = .done) :
    wait s t = some s := by
  simp [wait, h]

theorem commitLoad_value (s : SendState) (t : Token) (reg : Nat)
    (h : s.status t = .done) :
    (commitLoad s t reg).regs reg = s.result t := by
  simp [commitLoad, h]

theorem commitStore_value (s : SendState) (t : Token) (addr : Nat)
    (h : s.status t = .done) :
    (commitStore s t addr).mem addr = s.result t := by
  simp [commitStore, h]

theorem loadPipeline_value (s : SendState) (reg addr : Nat) :
    (loadPipeline s reg addr).regs reg = s.mem addr := by
  unfold loadPipeline issueLoad complete commitLoad
  simp

theorem loadPipeline_mem (s : SendState) (reg addr : Nat) :
    (loadPipeline s reg addr).mem = s.mem := by
  unfold loadPipeline issueLoad complete commitLoad
  simp

theorem storePipeline_value (s : SendState) (addr : Nat) (val : Word) :
    (storePipeline s addr val).mem addr = val := by
  unfold storePipeline issueStore complete commitStore
  simp

theorem addOnePipeline_value (s : SendState) (addr reg tmp : Nat) :
    (addOnePipeline s addr reg tmp).mem addr = s.mem addr + 1 := by
  unfold addOnePipeline storePipeline issueStore complete commitStore
  simp [loadPipeline, issueLoad, complete, commitLoad]

theorem addOnePipeline_frame (s : SendState) (addr reg tmp n : Nat)
    (hn : n ≠ addr) :
    (addOnePipeline s addr reg tmp).mem n = s.mem n := by
  unfold addOnePipeline storePipeline issueStore complete commitStore
  simp [loadPipeline, issueLoad, complete, commitLoad, hn]


/-- Negative test: a load that has been issued but not completed stalls; a
naive wait cannot observe the value early. -/
theorem wait_issueLoad_stalls (s : SendState) (reg addr : Nat) :
    wait (issueLoad s reg addr) s.next = none := by
  simp [wait, issueLoad]

theorem wait_issueStore_stalls (s : SendState) (addr : Nat) (val : Word) :
    wait (issueStore s addr val) s.next = none := by
  simp [wait, issueStore]

/-- A premature commit writes nothing: the token is still pending. -/
theorem commitLoad_pending (s : SendState) (t : Token) (reg : Nat)
    (h : s.status t = .pending) :
    commitLoad s t reg = s := by
  simp [commitLoad, h]

theorem commitStore_pending (s : SendState) (t : Token) (addr : Nat)
    (h : s.status t = .pending) :
    commitStore s t addr = s := by
  simp [commitStore, h]

end IntelGpu
