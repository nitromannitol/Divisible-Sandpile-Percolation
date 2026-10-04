# Audit report — `lem-weighted-exp-conc`

Batch A, 2026-10-04. Independent refute-first audit; the auditor wrote none of
this code and edited no Lean file. Manifest state is unchanged.

| field | value |
|---|---|
| node id | `lem-weighted-exp-conc` |
| export | `Sandpile.Frozen.weighted_exp_concentration` |
| file | `Sandpile/Frozen/WeightedExpConcentration.lean` |
| state | `SEALED` |
| kind | `theorem` |
| source | sandpile.tex:1345-1405 (label `lem:weighted-exp-conc`) |
| provider | `Sandpile.Frozen.weighted_exp_concentration` |
| verdict | **PASS** |

## 1. Statement integrity

Frozen block: `theorem Sandpile.Frozen.weighted_exp_concentration` with no
parameters and four top-level conjuncts `(a)–(d)`, exactly the paper's four parts:
(a) the `Lᵖ` bound for `p ≥ 2` with `C = C(p)` bound before `N`, the measures, `F`, `ℓ`;
(b) the sub-Gaussian/sub-exponential tail bound with `c,C` depending only on `θ₀,K₀`;
(c) the log-moment-generating-function bound; (d) the exponential-moment bound on
`F - E F`. The Lipschitz-in-resampling hypothesis is the everywhere form of the paper's
a.s. inequality (`|F ξ - F(update ξ i y)| ≤ ℓ i |ξ i - y|`); `‖ℓ‖_{ℓ²}`, `‖ℓ‖_{ℓ∞}` are
`lTwoNorm`, `lInfNorm`; `∃ i, ℓ i ≠ 0` keeps both norms positive; the exponential-moment
parts add `Integrable (exp (θ₀|z|))` so the integral is not the junk zero. This is a
faithful, term-by-term transcription.

## 2. Proof and axiom closure

The proof discharges (a) from `LatticeProb.exists_lp_square_pi` and (b), (c), (d)
from the registered providers `LatticeProb.weighted_exp_conc_tail`,
`LatticeProb.weighted_exp_conc_mgf` and the `Lp`/mgf machinery. It is a short chain over
the shared library. Compiles; `clean lem-weighted-exp-conc`.

## 3. Non-vacuity / junk

The hypotheses are satisfiable: `N = 1`, `μ = gaussianReal 0 1`, `F ξ = ξ₀`, `ℓ = 1`
satisfy the Lipschitz and moment hypotheses for every part. The conclusions are genuine
inequalities and moment bounds; the added integrability clauses in (c)/(d) prevent the
Bochner-integral junk value `log 0 = 0` from satisfying the bound. No non-summable
`tsum` is bounded without an explicit summability/moment hypothesis.

## 4. Citations

The node carries no `External` hypothesis beyond the paper anchor; all providers are
library theorems. Genuine.

## Machine evidence

- `lake build Sandpile` → `Build completed successfully (10229 jobs).`
- `python3 tools/check_axioms.py` → `clean lem-weighted-exp-conc`; overall `99 clean, 0 depend
  on sorryAx, 0 unresolved`, `check_axioms: OK (all closures match their
  registered states)`. `#print axioms Sandpile.Frozen.weighted_exp_concentration` resolves to
  `{propext, Classical.choice, Quot.sound}`.
- `python3 tools/check_manifest.py` → `OK (99 nodes, 0 unsealed)`; the frozen
  block of this node hashes to the manifest `frozen_sha256` and parses as the
  unique declaration `Sandpile.Frozen.weighted_exp_concentration`.
- `python3 tools/check_warnings.py` → `OK (0 registered sorry warnings)`.
- `python3 tools/check_clauses.py` / `check_exponents.py` / `check_constants.py`
  → `OK` (this node is covered by each).

## Verdict

**PASS.** Statement faithful, proof compiles with the standard axiom closure,
hypotheses satisfiable and conclusion non-junk, citations genuine.
