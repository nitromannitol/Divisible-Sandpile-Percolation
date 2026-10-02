# Contributing / Building notes

This repository is primarily a finished artifact rather than an actively
solicited collaborative project, but issues and pull requests are welcome.

## Building locally

```bash
lake exe cache get   # first time: prebuilt Mathlib
lake build           # compile the project
```

The production build is required to emit no Lean or linter warnings
(`python3 tools/check_warnings.py`).  The twelve Mathlib-only files
`SandpileAudit/*/Challenge.lean` are the sole exception: each contains one documented
statement-level `sorry`, checked against its completed solution by
`leanprover/comparator`.

A few practical notes for working with this development:

- **Never run `lake clean`.**  It wipes the Mathlib oleans and forces a
  multi-hour rebuild from source.  To force a project-only rebuild, remove the
  project build artifacts under `.lake/build/lib/lean/Sandpile` (and the
  corresponding `.lake/build/ir/Sandpile`) and re-run `lake build`.

- **Per-file rebuilds.**  Lake invalidates by content hash, not mtime, so
  `touch` does nothing; delete the specific `.olean` under
  `.lake/build/lib/lean/` and rebuild the module.

- **Frozen statements.**  The text between `-- FROZEN-STATEMENT-BEGIN` and
  `-- FROZEN-STATEMENT-END` in `Sandpile/Frozen/` and `Sandpile/External/` is
  pinned by the SHA-256 recorded in `ledger/manifest.yaml`.  A change there
  must be registered with `python3 tools/freeze.py` and shows up in
  `python3 tools/check_manifest.py`; proofs after the end marker may be
  changed freely.

- **The main results** are in `Sandpile/MainTheorems.lean`; the axiom audit is
  `lake build Sandpile.Meta.AxiomsAudit`, and the comparator surface is
  `lake build SandpileAudit`.

## Elaboration policy for new files

These rules apply to new Lean files; they keep elaboration cheap and predictable
in a development of this size.

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
- Never run `lake clean` (see above).
