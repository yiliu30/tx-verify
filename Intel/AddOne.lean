-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.Asm

@[expose] public section

/-!
# `add_one`: the IGC SIMD32 core

The modeled IGC kernel contains this user-code sequence:

```
load.ugm.d32.a64  r12:2 [r7:4]
add               r14.0 r12.0 1
store.ugm.d32.a64 [r7:4] r14:2
send.gtwy ...     EOT
```

The model below verifies the single-lane functional core: if `r0` holds the
byte address and the old word at that address is `v`, the sequence leaves
`v + 1` at that address and terminates. The compiler-generated prolog and
the SIMD32 lane mapping are explicit assumptions of this first kernel.
-/

namespace IntelGpu

def core : List Instr :=
  [.load32 1 0, .addImm 2 1 1, .store32 0 2, .eot]

structure AddOnePre (s : State) (addr : Addr) (v : Word) : Prop where
  regAddr : s.addrRegs 0 = addr
  memAt : load32 s.mem addr.toNat = v
  running : s.halted = false
  aligned : addr.toNat % 4 = 0

def AddOnePost (s0 s : State) (addr : Addr) (v : Word) : Prop :=
  s.halted = true ∧
  load32 s.mem addr.toNat = v + 1 ∧
  (∀ n, n ≠ addr.toNat / 4 → s.mem n = s0.mem n)

theorem core_correct (s : State) (addr : Addr) (v : Word) (h : AddOnePre s addr v) :
    AddOnePost s (run s core) addr v := by
  unfold AddOnePost core run
  simp [step, h.regAddr, h.memAt, h.running, load32_store32_same]
  intro n hn
  exact store32_frame s.mem addr.toNat (v + 1) n hn


end IntelGpu
