# Verification visualization

`verification.html` is a self-contained page (no external resources) that
visualizes the SYCL-TLA GEMM verification stack: the pipeline from the
imported assembly to the bit-exact hardware runs, the stage timeline
199-243 with their PRs, the headline verified claims and the trusted base.

Open it in any browser. The numbers reflect stage 243: 2252 decoded
statements, 2219 Lean theorems, 197 build jobs, four bit-exact hardware
sizes and a re-dump sha256 match.
