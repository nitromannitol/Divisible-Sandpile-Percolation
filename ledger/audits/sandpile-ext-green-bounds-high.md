# Audit report — `ext-green-bounds-high`

Batch A, 2026-10-04. Independent refute-first audit; the auditor wrote none of
this code and edited no Lean file. Manifest state is unchanged.

| field | value |
|---|---|
| node id | `ext-green-bounds-high` |
| export | `Sandpile.External.greenBoundsHigh` |
| file | `Sandpile/External/GreenBoundsHighProved.lean` |
| state | `SEALED` |
| kind | `theorem` |
| source | external input: Lawler-Limic Theorem 4.3.1 and Lawler Chapter 3, the `d ≥ 5` estimates of `ssec:green-estimates` |
| provider | `Sandpile.External.greenBoundsHigh` |
| verdict | **PASS** |

## 1. Statement integrity

Frozen block: `theorem Sandpile.External.greenBoundsHigh : Sandpile.External.GreenBoundsHigh`.
`GreenBoundsHigh` (frozen in `Sandpile/External/GreenBoundsHigh.lean`) is the exact
transcription of `eq:dgt4-green-tail`, `eq:dgt4-green-l2`, `eq:dgt4-tail-kernel`,
`eq:dgt4-intersection-first-moment` and `eq:dgt4-intersection-second-moment` for
`d ≥ 5`. Each intersection clause asserts summability before bounding the `tsum`
(`Summable … ∧ (∑' …) ≤ …`), so a non-summable `tsum` cannot supply the bound. The
hypothesis `5 ≤ d` matches `d ≥ 5` in the paper. All exponents `4-d`, `2-d`,
`(2-d)/2`, `(4-d)/2` appear as `rpow`s of the same shape as the paper.

## 2. Proof and axiom closure

The proof normalizes `d = k + 5`, rewrites the paper's two-point `green` as
`LatticeProb.srwGreenInf` (`green_eq_srwGreenInf`), converts negative natural rpow to
inverse powers (`rpow_cast_neg`, `rpow_half_neg`) and invokes the registered providers
`LatticeProb.exists_tsum_srwGreenInf_sq_tail_le`,
`LatticeProb.exists_srwGreenInf_sup_tail_le`, `LatticeProb.summable_srwGreenInf_sq`,
`LatticeProb.exists_srwTimeTail_le`, `LatticeProb.exists_tsum_srwTimeTail_sq_le`,
`LatticeProb.exists_tsum_srwGreenInf_mul_le`,
`LatticeProb.exists_tsum_srwGreenInf_crossed_le`. It imports the sibling node
`ext-variance-scale`. Compiles; `clean ext-green-bounds-high`.

## 3. Non-vacuity / junk

`5 ≤ d` is satisfiable (e.g. `d = 5`); the source walk is the simple random walk,
whose Green function and heat kernel exist in the shared library for every `d ≥ 1`.
The conclusion asserts summability of the relevant series, so it is not vacuous and
none of the `tsum`s is junk. Constants are bound before the summation indices.

## 4. Citations

No `External` hypothesis is carried; the node discharges an external input. The
only imports are the sibling `ext-variance-scale` and the shared library. Genuine.

## Machine evidence

- `lake build Sandpile` → `Build completed successfully (10229 jobs).`
- `python3 tools/check_axioms.py` → `clean ext-green-bounds-high`; overall `99 clean, 0 depend
  on sorryAx, 0 unresolved`, `check_axioms: OK (all closures match their
  registered states)`. `#print axioms Sandpile.External.greenBoundsHigh` resolves to
  `{propext, Classical.choice, Quot.sound}`.
- `python3 tools/check_manifest.py` → `OK (99 nodes, 0 unsealed)`; the frozen
  block of this node hashes to the manifest `frozen_sha256` and parses as the
  unique declaration `Sandpile.External.greenBoundsHigh`.
- `python3 tools/check_warnings.py` → `OK (0 registered sorry warnings)`.
- `python3 tools/check_clauses.py` / `check_exponents.py` / `check_constants.py`
  → `OK` (this node is covered by each).

## Verdict

**PASS.** Statement faithful, proof compiles with the standard axiom closure,
hypotheses satisfiable and conclusion non-junk, citations genuine.
