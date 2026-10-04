# Audit report — `thm-gaussian-upper-proved`

Batch A, 2026-10-04. Independent refute-first audit; the auditor wrote none of
this code and edited no Lean file. Manifest state is unchanged.

| field | value |
|---|---|
| node id | `thm-gaussian-upper-proved` |
| export | `Sandpile.External.gaussianUpper` |
| file | `Sandpile/External/GaussianUpperProved.lean` |
| state | `SEALED` |
| kind | `theorem` |
| source | the cited Gaussian upper bound on the heat kernel, proved from the shared library |
| provider | `Sandpile.External.gaussianUpper` |
| verdict | **PASS** |

## 1. Statement integrity

Frozen block: `theorem Sandpile.External.gaussianUpper : ∀ d, 1 ≤ d → ∃ C c > 0, ∀ n ≥ 1,
∀ x y, heatKernel d n x y ≤ C * n^(-d/2) * exp(-c * latticeDist x y^2 / n)`.
This is the first display `eq:rw-gaussian-upper` of `ssec:green-estimates`: a Gaussian
upper bound on the `n`-step heat kernel for `d ≥ 1`, with the constant bound before
`n`, `x`, `y` and both constants positive. The displacement is the Euclidean
`latticeDist`, matching `|x-y|` of the notation section (`sandpile.tex:678`).

## 2. Proof and axiom closure

The proof applies the registered provider `LatticeProb.srwHeat_gaussian` after the
bridge `Sandpile.External.heatKernel_eq_srwHeat`, then converts the library's graph norm
to `latticeDist` and rearranges the Gaussian exponent. C is `3^d * greenConst d` and
`c = 1/(8(1+2d))`, both shown positive. Compiles; `clean thm-gaussian-upper-proved`.

## 3. Non-vacuity / junk

`1 ≤ d`, `1 ≤ n`; satisfiable (`d = 1`, `n = 1`). The right-hand side is strictly
positive because `C > 0`, `c > 0`, and `exp` is positive; the inequality is a real
bound, not a junk equality. The `n^(-d/2)` is an honest `rpow` of a positive base.

## 4. Citations

No `External` hypothesis; this node is the discharge. The Gaussian bound is the
standard heat-kernel estimate the paper attributes to Lawler-Limic; the provider is a
library theorem. Genuine.

## Machine evidence

- `lake build Sandpile` → `Build completed successfully (10229 jobs).`
- `python3 tools/check_axioms.py` → `clean thm-gaussian-upper-proved`; overall `99 clean, 0 depend
  on sorryAx, 0 unresolved`, `check_axioms: OK (all closures match their
  registered states)`. `#print axioms Sandpile.External.gaussianUpper` resolves to
  `{propext, Classical.choice, Quot.sound}`.
- `python3 tools/check_manifest.py` → `OK (99 nodes, 0 unsealed)`; the frozen
  block of this node hashes to the manifest `frozen_sha256` and parses as the
  unique declaration `Sandpile.External.gaussianUpper`.
- `python3 tools/check_warnings.py` → `OK (0 registered sorry warnings)`.
- `python3 tools/check_clauses.py` / `check_exponents.py` / `check_constants.py`
  → `OK` (this node is covered by each).

## Verdict

**PASS.** Statement faithful, proof compiles with the standard axiom closure,
hypotheses satisfiable and conclusion non-junk, citations genuine.
