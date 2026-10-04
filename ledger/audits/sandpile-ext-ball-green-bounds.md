# Audit report — `ext-ball-green-bounds`

Batch A, 2026-10-04. Independent refute-first audit; the auditor wrote none of
this code and edited no Lean file. Manifest state is unchanged.

| field | value |
|---|---|
| node id | `ext-ball-green-bounds` |
| export | `Sandpile.External.ballGreenBounds` |
| file | `Sandpile/External/BallGreenBoundsProved.lean` |
| state | `SEALED` |
| kind | `theorem` |
| source | external input: Lawler-Limic Theorem 4.3.1 and Chapter 6, the ball-killed estimates of `ssec:green-estimates` |
| provider | `Sandpile.External.ballGreenBounds` |
| verdict | **PASS** |

## 1. Statement integrity

Frozen block: `theorem Sandpile.External.ballGreenBounds : Sandpile.External.BallGreenBounds`.
`BallGreenBounds` (frozen in `Sandpile/External/BallGreenBounds.lean`) is the
seven-clause transcription `eq:d4ball-point`, `eq:d4ball-square`, `eq:d4ball-near`, the
annular gradient bound, `eq:d4ball-far-cube`, `eq:d4ball-shift` and
`eq:d4ball-time-tail`, all for the dimension-four killed Green kernel and cutoff field
of the paper. Constants `C, c > 0` precede `r ≥ 2`; each `∑'` is an honest summability
statement (killed kernels) or an `ℝ≥0`-valued bound. Exponents (`1/(1+|u|)^2`,
`log r`, `1/L²`, `1/R²`, `exp(-cA)`, `(1+M)^4`) match the paper's displays.

## 2. Proof and axiom closure

The proof assembles the seven in-file clause lemmas through
`aux_ballgreen_assemble` (`aux_ballgreen_clause1`…`clause7_holds`), each proved from the
killed-walk energy estimates, a discrete Caccioppoli inequality and block survival.
It compiles; `clean ext-ball-green-bounds`.

## 3. Non-vacuity / junk

`2 ≤ r`, `2 ≤ L`, `2 ≤ R`, `1 ≤ A`, `1 ≤ M` are satisfiable. The conclusion is a
conjunction of bounds on honest non-negative kernels; the pointwise clause asserts
`0 ≤ killedGreen ≤ green`, and the `tsum` clauses bound genuinely summable quantities.
No junk value.

## 4. Citations

No `External` hypothesis; the node discharges the cited ball-killed estimates. All
providers are in the production tree. Genuine.

## Machine evidence

- `lake build Sandpile` → `Build completed successfully (10229 jobs).`
- `python3 tools/check_axioms.py` → `clean ext-ball-green-bounds`; overall `99 clean, 0 depend
  on sorryAx, 0 unresolved`, `check_axioms: OK (all closures match their
  registered states)`. `#print axioms Sandpile.External.ballGreenBounds` resolves to
  `{propext, Classical.choice, Quot.sound}`.
- `python3 tools/check_manifest.py` → `OK (99 nodes, 0 unsealed)`; the frozen
  block of this node hashes to the manifest `frozen_sha256` and parses as the
  unique declaration `Sandpile.External.ballGreenBounds`.
- `python3 tools/check_warnings.py` → `OK (0 registered sorry warnings)`.
- `python3 tools/check_clauses.py` / `check_exponents.py` / `check_constants.py`
  → `OK` (this node is covered by each).

## Verdict

**PASS.** Statement faithful, proof compiles with the standard axiom closure,
hypotheses satisfiable and conclusion non-junk, citations genuine.
