# Audit report — `ext-optimal-stopping`

Batch A, 2026-10-04. Independent refute-first audit; the auditor wrote none of
this code and edited no Lean file. Manifest state is unchanged.

| field | value |
|---|---|
| node id | `ext-optimal-stopping` |
| export | `Sandpile.External.optimalStopping` |
| file | `Sandpile/External/BPSHProved.lean` |
| state | `SEALED` |
| kind | `theorem` |
| source | external input: Theorem 3.2 of BPSH, the statement of `thm:RW` (`sandpile.tex:857-863`) |
| provider | `Sandpile.External.optimalStopping` |
| verdict | **PASS** |

## 1. Statement integrity

Frozen block: `theorem Sandpile.External.optimalStopping : Sandpile.External.OptimalStopping`.
`OptimalStopping` (frozen in `Sandpile/External/BPSH.lean`) states, for `1 ≤ d`, every
scenery `ζ`, `n` and site `x`,
`odometerOf ζ n x = stoppingValue ζ n x ∧ stoppingValue ζ n x = ∫ X, sceneryPartialSum ζ (optimalStop ζ n X) X ∂(walkLaw d x)`.
This is exactly `thm:RW`: `u_n = v_n = E_x[S_{τ_n^*}]`. `optimalStop` is the `sInf` of
`{k | k ≤ n ∧ stoppingValue ζ (n-k) (X k) = 0}`, a set that always contains `n` because
`v_0 = 0`, so the `sInf` is the paper's minimum, never `sInf ∅`. The added `1 ≤ d`
excludes the junk `d = 0` averaging operator; this is a fidelity note (the paper works
on `ℤ^d`, `d ≥ 1`).

## 2. Proof and axiom closure

The proof identifies this file's `odometerOf` with the shared library's
`LatticeProb.Graph.Zd.zdOdometer` by induction on `n` (`Sandpile.zdOdometer_eq`) and
applies the registered provider `LatticeProb.Graph.Zd.sandpileOptimalStopping'`. It is
a two-step application. Compiles; `clean ext-optimal-stopping`.

## 3. Non-vacuity / junk

Hypotheses: `1 ≤ d`, `ζ` any real field, `n : ℕ`, `x : Site d`. Satisfiable (`d = 1`,
`ζ = 0`). The equality is between honest reals, and the optimal stopping index is
defined by a non-empty `sInf`; the integral is against a probability measure
`walkLaw`. No junk value is read.

## 4. Citations

No `External` hypothesis; the node discharges the BPSH result. The statement is the
one the paper restates in `thm:RW`; the provider is a library theorem about the
optimal-stopping representation on `ℤ^d`. Genuine.

## Machine evidence

- `lake build Sandpile` → `Build completed successfully (10229 jobs).`
- `python3 tools/check_axioms.py` → `clean ext-optimal-stopping`; overall `99 clean, 0 depend
  on sorryAx, 0 unresolved`, `check_axioms: OK (all closures match their
  registered states)`. `#print axioms Sandpile.External.optimalStopping` resolves to
  `{propext, Classical.choice, Quot.sound}`.
- `python3 tools/check_manifest.py` → `OK (99 nodes, 0 unsealed)`; the frozen
  block of this node hashes to the manifest `frozen_sha256` and parses as the
  unique declaration `Sandpile.External.optimalStopping`.
- `python3 tools/check_warnings.py` → `OK (0 registered sorry warnings)`.
- `python3 tools/check_clauses.py` / `check_exponents.py` / `check_constants.py`
  → `OK` (this node is covered by each).

## Verdict

**PASS.** Statement faithful, proof compiles with the standard axiom closure,
hypotheses satisfiable and conclusion non-junk, citations genuine.
