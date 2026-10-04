# Audit report — `ext-intersection-second-moment`

Batch A, 2026-10-04. Independent refute-first audit; the auditor wrote none of
this code and edited no Lean file. Manifest state is unchanged.

| field | value |
|---|---|
| node id | `ext-intersection-second-moment` |
| export | `Sandpile.External.intersectionSecondMoment` |
| file | `Sandpile/External/IntersectionSecondMomentProved.lean` |
| state | `SEALED` |
| kind | `theorem` |
| source | sandpile.tex:1319-1324 (label `eq:dgt4-intersection-second-moment`; Lawler, Intersections of Random Walks, Theorem 3.3.2 pp. 95-97) |
| provider | `Sandpile.External.intersectionSecondMoment` |
| verdict | **PASS** |

## 1. Statement integrity

Frozen block: `theorem Sandpile.External.intersectionSecondMoment :
Sandpile.External.IntersectionSecondMoment`.
`IntersectionSecondMoment` (frozen in `Sandpile/External/IntersectionSecondMoment.lean`)
states, for `d ≥ 5`, the existence of `C > 0` with
`∫⁻X ∫⁻Y interCount X Y ^ 2 ∂(walkLaw d y) ∂(walkLaw d x) ≤
ENNReal.ofReal (C * (1 + latticeNorm (x - y))^(4-d))`.
`interCount` is the `ℝ≥0∞`-valued count `∑_{i,j} 1_{X_i = Y_j}`, deliberately infinite
valued so an infinite count is not rounded to zero. This is exactly
`eq:dgt4-intersection-second-moment` with the constant before the starting sites and the
paper's exponent `4-d`.

## 2. Proof and axiom closure

The proof applies the registered in-repo provider `Sandpile.lintegral_interCount_sq_le`
after installing `NeZero d` from `5 ≤ d`. It is a short application. Compiles; `clean
ext-intersection-second-moment`.

## 3. Non-vacuity / junk

`5 ≤ d` is satisfiable; both walks exist on any `Site d`. `interCount` is an `ℝ≥0∞`
`tsum`, so it is monotone and never takes a junk real value; the bound is
`ENNReal.ofReal` of a finite positive number. Non-vacuous.

## 4. Citations

No `External` hypothesis; the node discharges the cited Lawler estimate. The provider
`Sandpile.lintegral_interCount_sq_le` is in the production tree. Genuine.

## Machine evidence

- `lake build Sandpile` → `Build completed successfully (10229 jobs).`
- `python3 tools/check_axioms.py` → `clean ext-intersection-second-moment`; overall `99 clean, 0 depend
  on sorryAx, 0 unresolved`, `check_axioms: OK (all closures match their
  registered states)`. `#print axioms Sandpile.External.intersectionSecondMoment` resolves to
  `{propext, Classical.choice, Quot.sound}`.
- `python3 tools/check_manifest.py` → `OK (99 nodes, 0 unsealed)`; the frozen
  block of this node hashes to the manifest `frozen_sha256` and parses as the
  unique declaration `Sandpile.External.intersectionSecondMoment`.
- `python3 tools/check_warnings.py` → `OK (0 registered sorry warnings)`.
- `python3 tools/check_clauses.py` / `check_exponents.py` / `check_constants.py`
  → `OK` (this node is covered by each).

## Verdict

**PASS.** Statement faithful, proof compiles with the standard axiom closure,
hypotheses satisfiable and conclusion non-junk, citations genuine.
