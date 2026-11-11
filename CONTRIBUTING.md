# Contributing and building

This repository is mainly a finished artifact, the formalization of one paper, but issues and
pull requests are welcome.

## Building locally

```bash
lake exe cache get   # first time: prebuilt mathlib
lake build           # compile the project
```

The toolchain is pinned in `lean-toolchain`. The production build is required to emit no Lean
or linter warnings (`python3 tools/check_warnings.py`). The twelve mathlib-only files
`SandpileAudit/*/Challenge.lean` are the only files with a `sorry`: each contains one
documented statement-level `sorry`, checked against its completed solution by
`leanprover/comparator`. `lake build Sandpile` builds the library and
`lake build SandpileAudit` the comparator libraries.

## The main results and the axiom audit

The twelve main results are in `Sandpile/MainTheorems.lean`. To print their axiom reports:

```bash
lake build Sandpile.Meta.AxiomsAudit   # the twelve main theorems
python3 tools/check_axioms.py          # the axiom closure of every registered statement
```

`Sandpile/Meta/AxiomsAudit.lean` is not imported by the library root, because a
`#print axioms` command runs again whenever its module is rebuilt. Each report must list
exactly `propext`, `Classical.choice` and `Quot.sound`; the `Axiom audit` step of the CI
workflow fails on any warning or `sorry`, and `tools/check_axioms.py` fails on `sorryAx`. The
checkers in `tools/` need Python 3 and PyYAML (`pip install pyyaml`).

## Conventions for Lean files

- No `sorry`, `admit` or new `axiom` in the library; `python3 tools/check_manifest.py` rejects
  them.
- **Frozen statements.** The text between `-- FROZEN-STATEMENT-BEGIN` and
  `-- FROZEN-STATEMENT-END` in `Sandpile/Frozen/` and `Sandpile/External/` is pinned by the
  SHA-256 recorded in `ledger/manifest.yaml`. A change there must be registered with
  `python3 tools/freeze.py` and shows up in `python3 tools/check_manifest.py`; proofs after
  the end marker may be changed freely. Statements refer to the paper by LaTeX label.
- New declarations go under `Sandpile/`. The dependencies under `.lake/packages/` are
  read-only.
- **Never run `lake clean`.** It wipes the mathlib oleans and forces a multi-hour rebuild from
  source. To force a project-only rebuild, remove the project build artifacts under
  `.lake/build/lib/lean/Sandpile` (and the corresponding `.lake/build/ir/Sandpile`) and re-run
  `lake build`.
- **Per-file rebuilds.** Lake invalidates by content hash, not modification time, so `touch`
  does nothing; delete the specific `.olean` under `.lake/build/lib/lean/` and rebuild the
  module.

### Elaboration policy for new files

These rules apply to new Lean files; they keep elaboration cheap and predictable in a
development of this size.

- Close arithmetic goals with named monotonicity lemmas and `calc`, not with
  `nlinarith`. In particular never call `nlinarith` on a goal that contains
  `Real.rpow` or `Real.exp`: when a nonlinear fact is needed, hoist it into a
  small `private` lemma over abstract real variables, so that those terms never
  enter a numeric tactic.
- Prefer the explicit `mul_le_mul_of_nonneg_*` / `add_le_add_*` lemmas to
  `gcongr` on goals over `ℝ`. Over `ℝ≥0∞` or `ℕ` the tactic is cheap and fine.
- Before `ring` or `field_simp` on an expression built with `set`, run
  `clear_value` on the bound names; otherwise the let-bodies are unfolded inside
  the tactic.
- Do not split a file, narrow its imports, or add an instance cache "for
  performance" without a warm profile before and after
  (`lake env lean --profile <file>`); the profiler's default 100 ms floor hides
  diffuse costs, so use `-D profiler.threshold=1` when hunting them.
- A default-budget failure is a design signal (usually a wrong lemma orientation
  or a `set`-bound term), not a reason to raise `maxHeartbeats`.
- Keep Lean files under 1500 lines.

## Comparators

Each pair under `SandpileAudit/<Pair>/` has a `Challenge.lean` that imports mathlib only, a
`Solution.lean`, a `SolutionBasic.lean` and a `comparator.json` that permits exactly
`propext`, `Classical.choice` and `Quot.sound`. Do not add a declaration to a challenge that
the statement does not need, and do not change a challenge without checking it against the
paper's statement. The command that runs a pair is in
[`SandpileAudit/README.md`](SandpileAudit/README.md) and
[`SandpileAudit/COMPARATOR_RUNS.md`](SandpileAudit/COMPARATOR_RUNS.md). A missing pair, a
missing tool or a failed kernel check is a failure.

## Continuous integration

- `build.yml` (**CI**) builds the library, rejects any warning or `sorry` warning, builds the
  axiom audit module, and runs `tools/check_manifest.py`.
- `comparator.yml` (**Comparator audit**) builds `SandpileAudit` and runs the comparator on all
  twelve pairs.

Both run on pushes to `main` that change Lean files, `tools/`, `paper/`, `ledger/`,
`formalization.yaml` or the build configuration, and can be started manually.
