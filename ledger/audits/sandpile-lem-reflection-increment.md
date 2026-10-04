# Audit report — `lem-reflection-increment`

Batch A, 2026-10-04. Independent refute-first audit; the auditor wrote none of
this code and edited no Lean file. Manifest state is unchanged.

| field | value |
|---|---|
| node id | `lem-reflection-increment` |
| export | `Sandpile.Frozen.reflection_increment` |
| file | `Sandpile/Frozen/ReflectionIncrement.lean` |
| state | `SEALED` |
| kind | `theorem` |
| source | sandpile.tex:899-905 (label `lem:reflection-increment`) |
| provider | `Sandpile.Frozen.reflection_increment` |
| verdict | **PASS** |

## 1. Statement integrity

Frozen block: `theorem Sandpile.Frozen.reflection_increment` with hypotheses
`1 ≤ d`, `IsProbabilityMeasure ν`, `Integrable id ν`, `∫ z ∂ν = 0`, plus
integrability of the odometer and of the reflection term, concluding the conjunction
`Monotone (meanOdometer …) ∧ (∀ t, increment at t+1 ≤ increment at t) ∧
(∀ t, increment = ∫ max 0 (-(scenery) - avg …))`. This transcribes the paper's three
assertions: `E u_t(0)` nondecreasing, concave in `t` (written as nonincreasing integer
increments, the form the paper's proof uses), and the reflection-increment identity.
Renamings are faithful (`meanOdometer`, `scenery`, `avg`, `max 0`). **Fidelity note:** the
two integrability hypotheses `hodo`/`hrefl` are added side conditions the paper leaves
implicit; they keep the increment identity from being an identity between junk zeros.

## 2. Proof and axiom closure

The proof rewrites `centeredMassLaw` as `massLaw` of the pushed-forward one-site law,
obtains the scenery's integrability and mean (`Sandpile.scenery_integrable_and_mean`), the
averaging identity (`Sandpile.integral_avg_odometer`), splits the increment
(`Sandpile.relax_eq_scenery`, `Sandpile.max_zero_eq`), and proves monotonicity and the
increment comparison from `Sandpile.odometer_le_succ` and
`Sandpile.avg_odometer_mono`. It is a moderately long but structured proof. Compiles;
`clean lem-reflection-increment`.

## 3. Non-vacuity / junk

The hypotheses are satisfiable: `ν = gaussianReal 0 1` is a probability measure with
integrable identity and zero mean; the added integrability clauses hold for the
sub-Gaussian odometer of that law. The conclusion is a conjunction of a monotonicity
statement and two real identities, not `True`; the integral is taken only under an
integrability hypothesis, so no `integral_undef = 0` junk value is read.

## 4. Citations

The node carries no `External` hypothesis (the `*Proved` external nodes are used only
as providers through `Sandpile.*` lemmas, not as assumptions). All citations are to the
paper anchor and the production tree. Genuine.

## Machine evidence

- `lake build Sandpile` → `Build completed successfully (10229 jobs).`
- `python3 tools/check_axioms.py` → `clean lem-reflection-increment`; overall `99 clean, 0 depend
  on sorryAx, 0 unresolved`, `check_axioms: OK (all closures match their
  registered states)`. `#print axioms Sandpile.Frozen.reflection_increment` resolves to
  `{propext, Classical.choice, Quot.sound}`.
- `python3 tools/check_manifest.py` → `OK (99 nodes, 0 unsealed)`; the frozen
  block of this node hashes to the manifest `frozen_sha256` and parses as the
  unique declaration `Sandpile.Frozen.reflection_increment`.
- `python3 tools/check_warnings.py` → `OK (0 registered sorry warnings)`.
- `python3 tools/check_clauses.py` / `check_exponents.py` / `check_constants.py`
  → `OK` (this node is covered by each).

## Verdict

**PASS.** Statement faithful, proof compiles with the standard axiom closure,
hypotheses satisfiable and conclusion non-junk, citations genuine.
