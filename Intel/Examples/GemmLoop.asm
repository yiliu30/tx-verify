// Canonical GEMM loop-body fixture. No compiler paths or device metadata.
_0_004:
load.ugm.d32.a64 r22:2 [r18:4]
load.ugm.d32.a64 r30:2 [r26:4]
mul r32.0 r22.0 r30.0
add r14.0 r14.0 r32.0
add r3.8 r3.8 1
jmpi _0_004
