-- SPDX-License-Identifier: Apache-2.0
import Lake
open Lake DSL

package txverify where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0"

@[default_target]
lean_lib PTX where
  moreLeanArgs := #["-s512000"]
  -- Mathlib's line-width linter (limit 100); with `--wfail` a longer line fails the build.
  -- `Tools/check_lean_text.py --max-width 100` (pre-commit) applies the same rule.
  leanOptions := #[⟨`weak.linter.style.longLine, true⟩]
  globs := #[.submodules `Core, .submodules `Assumption, .submodules `Lemmas,
    .submodules `Tactics, .submodules `Tests, .submodules `Kernels.CopyDynamic,
    .submodules `Kernels.CopyLdg, .submodules `Kernels.RowSum, .submodules `Kernels.BlockSum,
    .submodules `Kernels.RmsNorm, .submodules `Kernels.TmaCopy,
    .submodules `Kernels.TcGemm, .submodules `Kernels.Fp16Gemm8192,
    .submodules `Kernels.FlashAttn4Fwd, .submodules `Kernels.AddOne,
    .submodules `Kernels.FlashMlaSparseDecodeH64, .submodules `Kernels.InklingRelDecode,
    .submodules `Kernels.TmlFa4Fwd]

lean_lib Intel where
  globs := #[.submodules `Intel]
  leanOptions := #[⟨`weak.linter.style.longLine, true⟩]
