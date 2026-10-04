# Audit report — `lem-recursion`

Batch A, 2026-10-04. Independent refute-first audit; the auditor wrote none of
this code and edited no Lean file. Manifest state is unchanged.

| field | value |
|---|---|
| node id | `lem-recursion` |
| export | `Sandpile.Frozen.odometer_recursion` |
| file | `Sandpile/Frozen/Recursion.lean` |
| state | `SEALED` |
| kind | `theorem` |
| source | sandpile.tex:817-822 (label `lem:recursion`) |
| provider | `Sandpile.Frozen.odometer_recursion` |
| verdict | **PASS** |

## 1. Statement integrity

Frozen block: `theorem Sandpile.Frozen.odometer_recursion (d) (hd : 1 ≤ d) (σ) (n) (x) :
topplingOdometer d σ (n+1) x = max 0 ((1/(2*d)) * nbrSum (topplingOdometer d σ n) x + scenery d σ x)`.
This is the paper's displayed recursion `u_{n+1}(x) = ((1/2d)∑_{y∼x}u_n(y) + ζ(x))_+`
with `nbrSum` the `2d` neighbours, `scenery d σ x = (σ x - 1)/(2d)`, `max 0` the
positive part. The added `1 ≤ d` removes the junk `d = 0` (both `1/(2d)` and `ζ` would
be `0`); this is a fidelity note.

## 2. Proof and axiom closure

The proof is a single application of the registered provider
`Sandpile.topplingOdometer_recursion hd σ n x`. Compiles; `clean lem-recursion`.

## 3. Non-vacuity / junk

Satisfiable: `d = 1`, `σ = 0`, `n = 0`, `x = 0` satisfy the hypothesis and make the
identity non-trivial. The conclusion is an equality of honest reals (an odometer value
against a `max 0` term), not `True` or `0`.

## 4. Citations

The node carries no `External` hypothesis. The provider is an in-repo theorem, and the
statement is the paper's `lem:recursion`. Genuine.

## Machine evidence

- `lake build Sandpile` → `Build completed successfully (10229 jobs).`
- `python3 tools/check_axioms.py` → `clean lem-recursion`; overall `99 clean, 0 depend
  on sorryAx, 0 unresolved`, `check_axioms: OK (all closures match their
  registered states)`. `#print axioms Sandpile.Frozen.odometer_recursion` resolves to
  `{propext, Classical.choice, Quot.sound}`.
- `python3 tools/check_manifest.py` → `OK (99 nodes, 0 unsealed)`; the frozen
  block of this node hashes to the manifest `frozen_sha256` and parses as the
  unique declaration `Sandpile.Frozen.odometer_recursion`.
- `python3 tools/check_warnings.py` → `OK (0 registered sorry warnings)`.
- `python3 tools/check_clauses.py` / `check_exponents.py` / `check_constants.py`
  → `OK` (this node is covered by each).

## Verdict

**PASS.** Statement faithful, proof compiles with the standard axiom closure,
hypotheses satisfiable and conclusion non-junk, citations genuine.
