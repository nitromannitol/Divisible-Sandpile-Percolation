# Audit report — `ext-paired-local-clt-four`

Batch A, 2026-10-04. Independent refute-first audit; the auditor wrote none of
this code and edited no Lean file. Manifest state is unchanged.

| field | value |
|---|---|
| node id | `ext-paired-local-clt-four` |
| export | `Sandpile.External.pairedLocalCLTFour` |
| file | `Sandpile/External/PairedLocalCLTFourProved.lean` |
| state | `SEALED` |
| kind | `theorem` |
| source | sandpile.tex:1145-1172: Lawler-Limic Theorem 2.1.3 Eq. (2.8), paired dimension-four estimate |
| provider | `Sandpile.External.pairedLocalCLTFour` |
| verdict | **PASS** |

## 1. Statement integrity

Frozen block: `theorem Sandpile.External.pairedLocalCLTFour :
Sandpile.External.PairedLocalCLTFour`.
`PairedLocalCLTFour` (frozen in `Sandpile/External/PairedLocalCLTFour.lean`) states the
summable dimension-four remainder the paper's proof of `lem:d4-double-heat-kernel`
calls "summable error": there is `C > 0` with, for every `n ≥ 1` and sites `x y`,
`|p_n(x,y) + p_{n+1}(x,y) - 8/(π² n²) exp(-2|x-y|²/n)| ≤ C/n³`. The constant precedes
`n`, `x`, `y`; `1 ≤ n` keeps denominators nonzero; the squared distance is the
coordinate sum. This is the `k = 4` specialization of the cited estimate and includes
the parity factor by pairing two successive times.

## 2. Proof and axiom closure

The proof is a longer Fourier/torus computation (`torusIntegral_pair_gaussian_approx_le`,
Fourier inversion `heatKernel_eq_fourierIntegral`, parity decomposition) establishing the
`n⁻³` bound with an explicit constant. It compiles; `clean ext-paired-local-clt-four`.

## 3. Non-vacuity / junk

`n ≥ 1` is satisfiable; the conclusion is an absolute-value bound with an explicit
positive constant, so it is a genuine estimate. The exponential is strictly positive and
the denominators are nonzero. No junk.

## 4. Citations

No `External` hypothesis; the node discharges the cited paired estimate. The provider
is the in-repo Fourier machinery. Genuine.

## Machine evidence

- `lake build Sandpile` → `Build completed successfully (10229 jobs).`
- `python3 tools/check_axioms.py` → `clean ext-paired-local-clt-four`; overall `99 clean, 0 depend
  on sorryAx, 0 unresolved`, `check_axioms: OK (all closures match their
  registered states)`. `#print axioms Sandpile.External.pairedLocalCLTFour` resolves to
  `{propext, Classical.choice, Quot.sound}`.
- `python3 tools/check_manifest.py` → `OK (99 nodes, 0 unsealed)`; the frozen
  block of this node hashes to the manifest `frozen_sha256` and parses as the
  unique declaration `Sandpile.External.pairedLocalCLTFour`.
- `python3 tools/check_warnings.py` → `OK (0 registered sorry warnings)`.
- `python3 tools/check_clauses.py` / `check_exponents.py` / `check_constants.py`
  → `OK` (this node is covered by each).

## Verdict

**PASS.** Statement faithful, proof compiles with the standard axiom closure,
hypotheses satisfiable and conclusion non-junk, citations genuine.
