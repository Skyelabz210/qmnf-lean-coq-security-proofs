import Lake
open Lake DSL

package «qmnf-proofs» where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «QMNFProofs» where
  globs := #[.submodules `QMNFProofs]
