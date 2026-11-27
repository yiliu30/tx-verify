-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaMovExec

@[expose] public section

/-!
# Running a sequence of predicated moves

`Intel.TlaMovExec` executes one move. This module sequences moves on the
register file and proves the entry effect of the first two instructions of the
SYCL-TLA GEMM: the prologue zeroes `r127` for 16 elements and the id move
copies `r1` into `r2` for 8 elements, with everything else framed.
-/

namespace IntelGpu

/-- The first prologue move. -/
def prologueMov : TlaMov :=
  ⟨⟨16, 0, true⟩, .reg ⟨127, 0, 0, 1, 1, 1⟩, .imm 0 .ud⟩

/-- The id move. -/
def idMov : TlaMov :=
  ⟨⟨8, 0, true⟩, .reg ⟨2, 0, 0, 1, 1, 1⟩, .reg ⟨1, 0, 0, 1, 1, 0⟩⟩

/-- Run a list of moves in order. -/
def tlaMovRun : List TlaMov → RegFile → RegFile
  | [], rf => rf
  | m :: ms, rf => tlaMovRun ms (tlaMovStep rf m)

theorem tlaMovRun_nil (rf : RegFile) : tlaMovRun [] rf = rf := rfl

theorem tlaMovRun_cons (m : TlaMov) (ms : List TlaMov) (rf : RegFile) :
    tlaMovRun (m :: ms) rf = tlaMovRun ms (tlaMovStep rf m) := rfl

/-- A run whose moves all avoid register `r` leaves `r` unchanged. -/
theorem tlaMovRun_frame (ms : List TlaMov) (rf : RegFile) (r : Nat)
    (h : ∀ m, m ∈ ms → ∀ g, m.dst = .reg g → r ≠ g.num) :
    ∀ j, tlaMovRun ms rf r j = rf r j := by
  induction ms generalizing rf with
  | nil => intro j; rfl
  | cons m ms ih =>
      intro j
      rw [tlaMovRun_cons]
      rw [ih (tlaMovStep rf m) (fun m' hm' g hg => h m' (by simp [hm']) g hg) j]
      cases hd : m.dst with
      | null =>
          cases m with
          | mk e dst src =>
              cases hd
              rw [tlaMovStep_null rf e src]
      | reg g =>
          cases m with
          | mk e dst src =>
              cases hd
              exact tlaMovStep_frame rf e g src r j
                (h ⟨e, .reg g, src⟩ (by simp) g rfl)

/-- The entry block: `r127` is zeroed for 16 elements, `r2` receives `r1`
for 8 elements, and every other register is framed. -/
theorem prologue_id_effect (rf : RegFile) :
    (∀ j, j < 16 → tlaMovRun [prologueMov, idMov] rf 127 j = 0) ∧
    (∀ j, j < 8 → tlaMovRun [prologueMov, idMov] rf 2 j = rf 1 j) ∧
    (∀ r j, r ≠ 127 → r ≠ 2 → tlaMovRun [prologueMov, idMov] rf r j = rf r j) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    rw [tlaMovRun_cons, tlaMovRun_cons]
    change tlaMovStep (tlaMovStep rf prologueMov)
      ⟨⟨8, 0, true⟩, .reg ⟨2, 0, 0, 1, 1, 1⟩,
        .reg ⟨1, 0, 0, 1, 1, 0⟩⟩ 127 j = 0
    rw [tlaMovStep_frame (tlaMovStep rf prologueMov) ⟨8, 0, true⟩
      ⟨2, 0, 0, 1, 1, 1⟩ (.reg ⟨1, 0, 0, 1, 1, 0⟩) 127 j (by decide)]
    exact prologue_zero rf j hj
  · intro j hj
    rw [tlaMovRun_cons, tlaMovRun_cons]
    change tlaMovStep (tlaMovStep rf prologueMov)
      ⟨⟨8, 0, true⟩, .reg ⟨2, 0, 0, 1, 1, 1⟩,
        .reg ⟨1, 0, 0, 1, 1, 0⟩⟩ 2 j = rf 1 j
    rw [id_move (tlaMovStep rf prologueMov) j hj]
    exact tlaMovStep_frame rf ⟨16, 0, true⟩ ⟨127, 0, 0, 1, 1, 1⟩
      (.imm 0 .ud) 1 j (by decide)
  · intro r j hr1 hr2
    rw [tlaMovRun_cons, tlaMovRun_cons]
    change tlaMovStep (tlaMovStep rf prologueMov)
      ⟨⟨8, 0, true⟩, .reg ⟨2, 0, 0, 1, 1, 1⟩,
        .reg ⟨1, 0, 0, 1, 1, 0⟩⟩ r j = rf r j
    rw [tlaMovStep_frame (tlaMovStep rf prologueMov) ⟨8, 0, true⟩
      ⟨2, 0, 0, 1, 1, 1⟩ (.reg ⟨1, 0, 0, 1, 1, 0⟩) r j (by simpa using hr2)]
    exact tlaMovStep_frame rf ⟨16, 0, true⟩ ⟨127, 0, 0, 1, 1, 1⟩
      (.imm 0 .ud) r j (by simpa using hr1)

end IntelGpu
