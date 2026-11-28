import Intel.GemmRealLoop

open IntelGpu

def mem64 (n : Nat) : Word :=
  if n < 4096 then BitVec.ofInt 32 (Int.ofNat n % 7 - 3)
  else if n < 8192 then BitVec.ofInt 32 (Int.ofNat (n - 4096) % 5 - 2)
  else 0

def leanChecksum : Nat :=
  (List.range 4096).foldl (fun acc idx =>
    let i : Word := BitVec.ofNat 32 (idx / 64)
    let j : Word := BitVec.ofNat 32 (idx % 64)
    (acc + (gemmDot mem64 0 4096 i j 0 0 64).toNat) % 2 ^ 32) 0

#eval (gemmDot mem64 0 4096 (0 : Word) (0 : Word) (0 : Word) 0 64).toNat
#eval (gemmDot mem64 0 4096 (1 : Word) (1 : Word) (0 : Word) 0 64).toNat
#eval (gemmDot mem64 0 4096 (63 : Word) (63 : Word) (0 : Word) 0 64).toNat
#eval leanChecksum
