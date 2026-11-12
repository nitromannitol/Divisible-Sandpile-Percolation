import Lake

open Lake DSL

package «divisible_sandpile» where

require «lattice-probability» from git
  "https://github.com/nitromannitol/Lattice-Probability.git" @ "260a90ab503aa32a5f0d37fd71e27f60983054ca"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "81a5d257c8e410db227a6665ed08f64fea08e997"

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

