# Audit report — `ext-variance-scale`

Batch A, 2026-10-04. Independent refute-first audit; the auditor wrote none of
this code and edited no Lean file. Manifest state is unchanged.

| field | value |
|---|---|
| node id | `ext-variance-scale` |
| export | `Sandpile.External.varianceScale` |
| file | `Sandpile/External/VarianceScaleProved.lean` |
| state | `SEALED` |
| kind | `theorem` |
| source | external input: finite-time variance scale, membrane correlations and window bounds of `ssec:green-estimates` (Lawler-Limic) |
| provider | `Sandpile.External.varianceScale` |
| verdict | **PASS** |

## 1. Statement integrity

Frozen block: `theorem Sandpile.External.varianceScale : Sandpile.External.VarianceScale`.
The body of `VarianceScale` (frozen in `Sandpile/External/VarianceScale.lean`) is a
three-conjunct transcription of `eq:Qt-table`, `eq:corr-bound` and the dimension-four
window/tail displays `eq:d4-window-l2`, `eq:d4-window-linfty`,
`eq:d4-full-window-bounds`. The summability of every `∑'` is structural: `greenTime`
is a finite sum of finitely supported heat kernels, so no non-summable `tsum` is
hidden. Exponents `varianceRate`, `corrRate` are matched definitionally (the proof
uses `rfl` bridges `Sandpile.varianceRate_eq`, `Sandpile.corrRate_eq`). This is a
cited input, so the transcription target is the cited estimates; the frozen `Prop`
records them with the paper's quantifier order (`∃ c C` before `∀ t`).

## 2. Proof and axiom closure

The proof is a short chain over the shared library: `greenTime_eq_srwGreen`,
`varianceRate_eq`, `corrRate_eq`, `windowKernel_eq_srwWindow`, `tsum_shift_sub`, then
the registered providers `LatticeProb.exists_tsum_srwGreen_sq_bounds`,
`LatticeProb.exists_tsum_srwGreen_mul_le`, `LatticeProb.exists_tsum_srwWindow_sq_le`,
`LatticeProb.exists_tsum_srwGreen_four_sq_le`. It compiles and the export's closure is
exactly the three standard axioms (`clean ext-variance-scale`).

## 3. Non-vacuity / junk

Hypotheses are `1 ≤ d` (and `t ≥ 2`, `m ≥ 1`, `m ≤ n` inside the clauses); these are
satisfiable. The conclusion is a conjunction of honest two-sided bounds on `∑'`
quantities whose summability is structural, and of `Real.sqrt` factors that are
non-negative, so it is not a `True`-like or zero-like junk conclusion.

## 4. Citations

The node carries no `External` hypothesis; it *is* the discharge of an external
input. The cited source is the random-walk part of `ssec:green-estimates`; the proof
identifies this repository's two-point kernels with the shared library's
translation-invariant kernels (`heatKernel_eq_srwHeat`) and cites only library
theorems. No `External` is left assumed.

## Machine evidence

- `lake build Sandpile` → `Build completed successfully (10229 jobs).`
- `python3 tools/check_axioms.py` → `clean ext-variance-scale`; overall `99 clean, 0 depend
  on sorryAx, 0 unresolved`, `check_axioms: OK (all closures match their
  registered states)`. `#print axioms Sandpile.External.varianceScale` resolves to
  `{propext, Classical.choice, Quot.sound}`.
- `python3 tools/check_manifest.py` → `OK (99 nodes, 0 unsealed)`; the frozen
  block of this node hashes to the manifest `frozen_sha256` and parses as the
  unique declaration `Sandpile.External.varianceScale`.
- `python3 tools/check_warnings.py` → `OK (0 registered sorry warnings)`.
- `python3 tools/check_clauses.py` / `check_exponents.py` / `check_constants.py`
  → `OK` (this node is covered by each).

## Verdict

**PASS.** Statement faithful, proof compiles with the standard axiom closure,
hypotheses satisfiable and conclusion non-junk, citations genuine.
