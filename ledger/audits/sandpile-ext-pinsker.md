# Audit report — `ext-pinsker`

Batch A, 2026-10-04. Independent refute-first audit; the auditor wrote none of
this code and edited no Lean file. Manifest state is unchanged.

| field | value |
|---|---|
| node id | `ext-pinsker` |
| export | `Sandpile.External.pinsker` |
| file | `Sandpile/External/PinskerProved.lean` |
| state | `SEALED` |
| kind | `theorem` |
| source | sandpile.tex:2390 (as recorded; the invocation is at 2422): Pinsker's inequality, total variation against relative entropy |
| provider | `Sandpile.External.pinsker` |
| verdict | **PASS** |

## 1. Statement integrity

Frozen block: `theorem Sandpile.External.pinsker : Sandpile.External.Pinsker`.
`Pinsker` (frozen in `Sandpile/External/Pinsker.lean`) is the bounded form used by
`prop:fixed-scale-crossings`: for a measurable set `A` and `δ ≥ 0` with
`klDiv μ ν ≤ ENNReal.ofReal δ`, `|μ.real A - ν.real A| ≤ Real.sqrt (δ / 2)`. Relative
entropy is Mathlib's `InformationTheory.klDiv`; the `ENNReal.ofReal δ` hypothesis makes
the entropy finite, so the conclusion is never read through a collapsed `toReal`. This
is the paper's `P(…) - P_0(…) ≤ (L/(2𝔪R))√(E_0 𝓝)` in the single-set bounded form.
**Citation note N-1:** the manifest and the docstring cite line 2390, but the sentence
invoking Pinsker is at line 2422; the citation is genuine, the line anchor is off by 32
lines.

## 2. Proof and axiom closure

The proof is a direct application of the registered provider `LatticeProb.pinsker`
with the entropy bound. Compiles; `clean ext-pinsker`.

## 3. Non-vacuity / junk

Hypotheses are satisfiable: take `T` with two probability measures, `μ = ν` and
`δ = 0`, then both sides are `0`; non-degenerate instances exist. The conclusion bounds
a real total-variation difference by a genuine `Real.sqrt`, not a junk value.

## 4. Citations

The node carries no `External` hypothesis; it discharges the cited Pinsker input. The
provider is the shared library theorem. The only issue is the line number (N-1), which
does not affect the statement or proof.

## Machine evidence

- `lake build Sandpile` → `Build completed successfully (10229 jobs).`
- `python3 tools/check_axioms.py` → `clean ext-pinsker`; overall `99 clean, 0 depend
  on sorryAx, 0 unresolved`, `check_axioms: OK (all closures match their
  registered states)`. `#print axioms Sandpile.External.pinsker` resolves to
  `{propext, Classical.choice, Quot.sound}`.
- `python3 tools/check_manifest.py` → `OK (99 nodes, 0 unsealed)`; the frozen
  block of this node hashes to the manifest `frozen_sha256` and parses as the
  unique declaration `Sandpile.External.pinsker`.
- `python3 tools/check_warnings.py` → `OK (0 registered sorry warnings)`.
- `python3 tools/check_clauses.py` / `check_exponents.py` / `check_constants.py`
  → `OK` (this node is covered by each).

## Verdict

**PASS.** Statement faithful, proof compiles with the standard axiom closure,
hypotheses satisfiable and conclusion non-junk, citations genuine.
