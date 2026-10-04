# Audit report — `prop-finite-time-concentration-scale`

Batch A, 2026-10-04. Independent refute-first audit; the auditor wrote none of
this code and edited no Lean file. Manifest state is unchanged.

| field | value |
|---|---|
| node id | `prop-finite-time-concentration-scale` |
| export | `Sandpile.Frozen.finite_time_concentration_scale` |
| file | `Sandpile/Frozen/FiniteTimeConcentration.lean` |
| state | `SEALED` |
| kind | `theorem` |
| source | sandpile.tex:1462-1487 (label `prop:finite-time-concentration-scale`) |
| provider | `Sandpile.Frozen.finite_time_concentration_scale` |
| verdict | **PASS** |

## 1. Statement integrity

Frozen block: `theorem Sandpile.Frozen.finite_time_concentration_scale (ν) (hprob)` with
four top-level conjuncts: (1) `ζ ↦ odometerOf ζ t x` is convex on the whole vector space;
(2) the `ℓ²` Lipschitz bound with `Real.sqrt (∑' g_t(x,z)²) * Real.sqrt (∑' (ζ-η)²)`;
(3) the `Lᵖ` moment bound `≤ C * Var(V_t(0))^(p/2)` with `C` after `p` and the law;
(4) the covariance double inequality `0 ≤ Cov ≤ 2 Var(ζ(0)) ∑ᵤ g_n g_m`. The paper's
"in particular `Var(u_t(x)) ≤ C Var(V_t(0))`" is the `p = 2` instance of (3), as in the
paper. The added `Summable (ζ-η)²` hypothesis prevents the `ℓ²` norm from being the junk
`0`; `1 ≤ d` is a harmless standing hypothesis.

## 2. Proof and axiom closure

The proof discharges the four conjuncts with the in-repo providers
`Sandpile.odometerOf_convexOn`, `Sandpile.abs_odometerOf_sub_le_l2`,
`Sandpile.exists_odometer_moment_variance_uniform` (which produces the uniform `C`),
`Sandpile.covariance_odometerOf_nonneg` and `Sandpile.covariance_odometerOf_le`.
It is a short structured application. Compiles; `clean
prop-finite-time-concentration-scale`.

## 3. Non-vacuity / junk

Satisfiable: `ν = gaussianReal 0 1` satisfies the probability hypothesis; the clauses
for `p`, the `ℓ²` bound and the covariance bound have non-empty hypothesis sets. The
conclusion is a conjunction of an honest convexity statement and real inequalities; the
sums are over finitely supported `greenTime`, and the `ℓ²` sum has an explicit
summability hypothesis. No junk value.

## 4. Citations

The node carries no `External` hypothesis; all providers are in the production tree.
The paper anchor and constants match. Genuine.

## Machine evidence

- `lake build Sandpile` → `Build completed successfully (10229 jobs).`
- `python3 tools/check_axioms.py` → `clean prop-finite-time-concentration-scale`; overall `99 clean, 0 depend
  on sorryAx, 0 unresolved`, `check_axioms: OK (all closures match their
  registered states)`. `#print axioms Sandpile.Frozen.finite_time_concentration_scale` resolves to
  `{propext, Classical.choice, Quot.sound}`.
- `python3 tools/check_manifest.py` → `OK (99 nodes, 0 unsealed)`; the frozen
  block of this node hashes to the manifest `frozen_sha256` and parses as the
  unique declaration `Sandpile.Frozen.finite_time_concentration_scale`.
- `python3 tools/check_warnings.py` → `OK (0 registered sorry warnings)`.
- `python3 tools/check_clauses.py` / `check_exponents.py` / `check_constants.py`
  → `OK` (this node is covered by each).

## Verdict

**PASS.** Statement faithful, proof compiles with the standard axiom closure,
hypotheses satisfiable and conclusion non-junk, citations genuine.
