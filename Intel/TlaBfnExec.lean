-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.TlaBfnSend
public import Intel.TlaBlock2dExec

@[expose] public section

/-!
# Executing the bit-field and message forms

`TlaBfn.step` writes the bit-field result into the masked destination
elements. `tlaSendStep` appends a message to an abstract log; the final
`send.gtwy` of the dump carries `EOT`, so the log's last message is the
end-of-thread marker.
-/

namespace IntelGpu

/-- A `bfn` step writes the active destination elements. -/
theorem TlaBfn.step_value (rf : RegFile) (b : TlaBfn) (g : Grf)
    (hd : b.dst = .reg g) (i : Nat) (hd1 : g.hstride = 1)
    (ha : b.exec.elementActive i = true) :
    TlaBfn.step rf b g.num (g.dstIndex i) = b.value rf i := by
  unfold TlaBfn.step
  rw [hd]
  exact writeTlaMasked_element rf g b.exec (b.value rf) i hd1 ha

/-- A `bfn` step frames other registers. -/
theorem TlaBfn.step_frame (rf : RegFile) (b : TlaBfn) (g : Grf)
    (hd : b.dst = .reg g) (r j : Nat) (hr : r ≠ g.num) :
    TlaBfn.step rf b r j = rf r j := by
  unfold TlaBfn.step
  rw [hd]
  unfold writeTlaMasked
  simp [hr]

/-- The `bfn` form at PC 72. -/
def bfn72 : TlaBfn :=
  ⟨⟨16, 0, true⟩, .reg ⟨62, 0, 0, 1, 1, 1⟩, .reg ⟨16, 0, 0, 1, 0, 0⟩,
    .reg ⟨2, 0, 3, 0, 0, 0⟩, .reg ⟨2, 0, 9, 0, 1, 0⟩, .andOr⟩

/-- PC 72 computes `(r16[l] &&& r2.3) ||| r2.9`. -/
theorem bfn72_value (rf : RegFile) (l : Nat) :
    bfn72.value rf l = (rf 16 l &&& rf 2 3) ||| rf 2 9 := by
  simp [bfn72, TlaBfn.value, readTlaSrc, srcIndex]

/-- PC 72 writes its result into `r62`. -/
theorem bfn72_step_value (rf : RegFile) (i : Nat)
    (ha : bfn72.exec.elementActive i = true) :
    TlaBfn.step rf bfn72 62 i = (rf 16 i &&& rf 2 3) ||| rf 2 9 := by
  have h := TlaBfn.step_value rf bfn72 ⟨62, 0, 0, 1, 1, 1⟩ rfl i (by decide) ha
  have hd : (⟨62, 0, 0, 1, 1, 1⟩ : Grf).dstIndex i = i := by simp [Grf.dstIndex]
  rw [hd] at h
  rw [h, bfn72_value]

/-- A message emitted by `send.gtwy`. -/
structure TlaMsg where
  src : String
  payload : String
  eot : Bool
  deriving Repr, DecidableEq

def TlaSend.toMsg (s : TlaSend) : TlaMsg := ⟨s.src, s.payload, s.eot⟩

/-- Append one message to the log. -/
def tlaSendStep (log : List TlaMsg) (s : TlaSend) : List TlaMsg :=
  log ++ [s.toMsg]

theorem tlaSendStep_length (log : List TlaMsg) (s : TlaSend) :
    (tlaSendStep log s).length = log.length + 1 := by
  simp [tlaSendStep]

theorem tlaSendStep_getLast (log : List TlaMsg) (s : TlaSend) :
    (tlaSendStep log s).getLast? = some s.toMsg := by
  simp [tlaSendStep]

/-- The final `send.gtwy` at PC 2246. -/
def sendEot : TlaSend := ⟨⟨1, 0, true⟩, "null", "r112", "0x0", true⟩

theorem tlaSendStep_eot (log : List TlaMsg) :
    ((tlaSendStep log sendEot).getLast?).map (fun m => m.eot) = some true := by
  simp [tlaSendStep, TlaSend.toMsg, sendEot]

set_option maxRecDepth 1000000 in
/-- The two sends are a plain message followed by the EOT message. -/
theorem realTlaGemmSend_eots :
    realTlaGemmSend.map (fun s => s.eot) = [false, true] := by
  decide

end IntelGpu
