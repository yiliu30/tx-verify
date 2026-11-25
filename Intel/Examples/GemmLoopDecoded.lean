-- SPDX-License-Identifier: Apache-2.0
module

public import Intel.Decode
public import Intel.Examples.GemmLoop

@[expose] public section

namespace IntelGpu

def gemmLoopExpected : List IInstr :=
  [IInstr.label "_0_004",
   IInstr.load32 22 18,
   IInstr.load32 30 26,
   IInstr.mul 32 22 30,
   IInstr.add 14 14 32,
   IInstr.addImm 3 3 1,
   IInstr.jmpi "_0_004"]

theorem decode_gemmLoop : decodeProgram gemmLoop = some gemmLoopExpected := by
  rfl

end IntelGpu
