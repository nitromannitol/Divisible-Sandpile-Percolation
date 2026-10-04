# Audit report — `ext-gaussian-law-covariance`

Batch A, 2026-10-04. Independent refute-first audit; the auditor wrote none of
this code and edited no Lean file. Manifest state is unchanged.

| field | value |
|---|---|
| node id | `ext-gaussian-law-covariance` |
| export | `Sandpile.External.gaussianLawDeterminedByCovariance` |
| file | `Sandpile/External/GaussianLawCovarianceProved.lean` |
| state | `SEALED` |
| kind | `theorem` |
| source | sandpile.tex:2137-2138: a centred Gaussian planar field is determined in law by its covariance |
| provider | `Sandpile.External.gaussianLawDeterminedByCovariance` |
| verdict | **PASS** |

## 1. Statement integrity

Frozen block: `theorem Sandpile.External.gaussianLawDeterminedByCovariance :
Sandpile.External.GaussianLawDeterminedByCovariance`.
`GaussianLawDeterminedByCovariance` (frozen in
`Sandpile/External/GaussianLawCovariance.lean`) states that two centred Gaussian
processes on `Sandpile.Continuum.Space 2 → Ω → ℝ` with the same covariance have the
same `fieldLaw`. The paper at `sandpile.tex:2137-2138` asserts the unit-scale field is
stationary, sign-symmetric and invariant under `π/2` rotations and reflections; the
covariance-determines-law step is the classical fact supporting that invariance-in-law
claim. Hypotheses (Gaussian process, measurable, centred, equal covariance) are exactly
what the classical fact needs, and no integrability hypothesis is dropped because the
Gaussian clauses already give it.

## 2. Proof and axiom closure

The proof is a direct application of the registered provider
`LatticeProb.gaussianProcess_map_eq_of_covariance`. Compiles; `clean
ext-gaussian-law-covariance`.

## 3. Non-vacuity / junk

A centred Gaussian process on `Space 2` exists (e.g. white noise), and two copies have
equal covariance, so the hypotheses are satisfiable. The conclusion is an equality of
probability laws (pushforwards), not `True` or `0`, and `fieldLaw` is a genuine law. No
junk.

## 4. Citations

No `External` hypothesis; the node discharges a classical input. The citation to
`sandpile.tex:2137-2138` is the paper's invariance sentence that this fact supports;
the fact itself is standard and the provider is a library theorem. Genuine.

## Machine evidence

- `lake build Sandpile` → `Build completed successfully (10229 jobs).`
- `python3 tools/check_axioms.py` → `clean ext-gaussian-law-covariance`; overall `99 clean, 0 depend
  on sorryAx, 0 unresolved`, `check_axioms: OK (all closures match their
  registered states)`. `#print axioms Sandpile.External.gaussianLawDeterminedByCovariance` resolves to
  `{propext, Classical.choice, Quot.sound}`.
- `python3 tools/check_manifest.py` → `OK (99 nodes, 0 unsealed)`; the frozen
  block of this node hashes to the manifest `frozen_sha256` and parses as the
  unique declaration `Sandpile.External.gaussianLawDeterminedByCovariance`.
- `python3 tools/check_warnings.py` → `OK (0 registered sorry warnings)`.
- `python3 tools/check_clauses.py` / `check_exponents.py` / `check_constants.py`
  → `OK` (this node is covered by each).

## Verdict

**PASS.** Statement faithful, proof compiles with the standard axiom closure,
hypotheses satisfiable and conclusion non-junk, citations genuine.
