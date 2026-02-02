import Lake
open Lake DSL

package «qmnf_security_proofs» where
  version := v!"0.1.0"
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «SwarmProofs» where
  globs := #[.submodules `SwarmProofs]
