import Lake

open Lake DSL

package «divisible_sandpile» where

require «lattice-probability» from git
  "https://github.com/nitromannitol/Lattice-Probability.git" @ "f5e0412c1b144ea3f341d0dd64d66e9defe53b19"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "065356127b1dc0016f66b7283ce0ce2c4055aa55"

/-- The comparator audit surface (`SandpileAudit/*/Challenge.lean`,
`SandpileAudit/*/SolutionBasic.lean`, `SandpileAudit/*/Solution.lean` and
`SandpileAudit/Support/`).  Not a default target: it builds only on demand
(`lake build SandpileAudit`), so the ordinary build of `Sandpile` is unchanged. -/
lean_lib «SandpileAudit» where
  globs := #[.submodules `SandpileAudit]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.unusedVariables, true⟩,
    ⟨`linter.unusedSectionVars, true⟩,
    ⟨`linter.unusedSimpArgs, true⟩,
    ⟨`linter.unnecessarySimpa, true⟩,
    ⟨`linter.deprecated, true⟩
  ]

@[default_target]
lean_lib «Sandpile» where
  globs := #[.andSubmodules `Sandpile]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.unusedVariables, true⟩,
    ⟨`linter.unusedSectionVars, true⟩,
    ⟨`linter.unusedSimpArgs, true⟩,
    ⟨`linter.unnecessarySimpa, true⟩,
    ⟨`linter.deprecated, true⟩
  ]

