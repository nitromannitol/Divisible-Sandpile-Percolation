# Audit report — `ext-local-clt`

Batch A, 2026-10-04. Independent refute-first audit; the auditor wrote none of
this code and edited no Lean file. Manifest state is unchanged.

| field | value |
|---|---|
| node id | `ext-local-clt` |
| export | `Sandpile.External.localCLT` |
| file | `Sandpile/External/LocalCLTProved.lean` |
| state | `SEALED` |
| kind | `theorem` |
| source | external input: Lawler-Limic Theorem 2.1.3 Eq. (2.8), the local central limit theorem of `ssec:green-estimates` |
| provider | `Sandpile.External.localCLT` |
| verdict | **PASS** |

## 1. Statement integrity

Frozen block: `theorem Sandpile.External.localCLT : Sandpile.External.LocalCLT`.
`LocalCLT` (frozen in `Sandpile/External/LocalCLT.lean`) is the `ε`-`R₀` transcription of
`eq:lclt-parity` (`sandpile.tex:1145-1161`): for `1 ≤ d`, `0 < δ < T`, `C₀`, `ε > 0`
there is `R₀ > 0` such that for `R ≥ R₀` every admissible triple satisfies
`R^d |p_ℓ(x,y) - 2 R^{-d} p^{BM}_{ℓ/R²}(R^{-1}x, R^{-1}y)| ≤ ε`. The supremum is written
as the uniform bound, avoiding `sSup ∅`; `R₀ > 0` keeps every denominator nonzero; the
admissible-triple constraints (including `0 < heatKernel d ℓ x y`) are the paper's. The
`1 ≤ d` hypothesis excludes the junk `d = 0` recursion.

## 2. Proof and axiom closure

The proof is a longer chain over the shared library (Fourier inversion and a uniform
error bound), using `exists_uniform_error_bound_le`, `heatKernel_eq_fourierIntegral` and
the torus parity decomposition. It compiles; `clean ext-local-clt`.

## 3. Non-vacuity / junk

`δ`, `T`, `C₀`, `ε` are satisfiable (e.g. `δ = 1`, `T = 2`, `C₀ = 1`, `ε = 1`). The
conclusion is a genuine uniform error bound; the hypothesis set is non-empty for large
`R` (the parity class is non-empty). No junk value: the limit object is the honest
Brownian heat kernel, evaluated at time `ℓ/R² ≥ δ > 0`.

## 4. Citations

No `External` hypothesis; the node discharges the cited local CLT. The provider is the
shared library's Fourier/Gaussian-comparison machinery. Genuine.

## Machine evidence

- `lake build Sandpile` → `Build completed successfully (10229 jobs).`
- `python3 tools/check_axioms.py` → `clean ext-local-clt`; overall `99 clean, 0 depend
  on sorryAx, 0 unresolved`, `check_axioms: OK (all closures match their
  registered states)`. `#print axioms Sandpile.External.localCLT` resolves to
  `{propext, Classical.choice, Quot.sound}`.
- `python3 tools/check_manifest.py` → `OK (99 nodes, 0 unsealed)`; the frozen
  block of this node hashes to the manifest `frozen_sha256` and parses as the
  unique declaration `Sandpile.External.localCLT`.
- `python3 tools/check_warnings.py` → `OK (0 registered sorry warnings)`.
- `python3 tools/check_clauses.py` / `check_exponents.py` / `check_constants.py`
  → `OK` (this node is covered by each).

## Verdict

**PASS.** Statement faithful, proof compiles with the standard axiom closure,
hypotheses satisfiable and conclusion non-junk, citations genuine.
