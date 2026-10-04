# Audit report — `thm-max-displacement-proved`

Batch A, 2026-10-04. Independent refute-first audit; the auditor wrote none of
this code and edited no Lean file. Manifest state is unchanged.

| field | value |
|---|---|
| node id | `thm-max-displacement-proved` |
| export | `Sandpile.External.maxDisplacement` |
| file | `Sandpile/External/MaxDisplacementProved.lean` |
| state | `SEALED` |
| kind | `theorem` |
| source | the cited maximal-displacement estimate, proved from the shared library |
| provider | `Sandpile.External.maxDisplacement` |
| verdict | **PASS** |

## 1. Statement integrity

Frozen block: `theorem Sandpile.External.maxDisplacement : ∀ d, 1 ≤ d → ∃ C c > 0,
∀ n ≥ 1, ∀ R ≥ 1, ∀ x, walkLaw d x {X | ∃ k ≤ n, R ≤ latticeDist (X k) x} ≤
ENNReal.ofReal (C * exp(-c R^2 / n))`.
This is `eq:rw-max-displacement` (third display of `ssec:green-estimates`): a
sub-Gaussian tail bound for the maximal displacement of the walk up to time `n`. The
probability is an `ℝ≥0∞` measure and is compared with `ENNReal.ofReal` of an honest
finite real, so the bounded-comparison form never reads a real junk value.

## 2. Proof and axiom closure

The proof applies the registered provider `LatticeProb.exists_maxDisp_bound` and
uses monotonicity of measure along the containment
`{∃ k ≤ n, R ≤ latticeDist (X k) x} ⊆ {∃ k ≤ n, R ≤ graphNorm (X k - x)}` together with
`latticeDist_le_graphNorm`. Compiles; `clean thm-max-displacement-proved`.

## 3. Non-vacuity / junk

`1 ≤ d`, `1 ≤ n`, `1 ≤ R`; satisfiable. The conclusion is a genuine probability
bound (`ENNReal.ofReal` of a positive finite number); the null event is not the only
instance. No junk.

## 4. Citations

No `External` hypothesis; this node is the discharge of the cited maximal-displacement
estimate. The provider is the shared library's maximal-displacement theorem. Genuine.

## Machine evidence

- `lake build Sandpile` → `Build completed successfully (10229 jobs).`
- `python3 tools/check_axioms.py` → `clean thm-max-displacement-proved`; overall `99 clean, 0 depend
  on sorryAx, 0 unresolved`, `check_axioms: OK (all closures match their
  registered states)`. `#print axioms Sandpile.External.maxDisplacement` resolves to
  `{propext, Classical.choice, Quot.sound}`.
- `python3 tools/check_manifest.py` → `OK (99 nodes, 0 unsealed)`; the frozen
  block of this node hashes to the manifest `frozen_sha256` and parses as the
  unique declaration `Sandpile.External.maxDisplacement`.
- `python3 tools/check_warnings.py` → `OK (0 registered sorry warnings)`.
- `python3 tools/check_clauses.py` / `check_exponents.py` / `check_constants.py`
  → `OK` (this node is covered by each).

## Verdict

**PASS.** Statement faithful, proof compiles with the standard axiom closure,
hypotheses satisfiable and conclusion non-junk, citations genuine.
