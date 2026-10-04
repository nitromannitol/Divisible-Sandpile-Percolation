# Audit report — `thm-brownian-exists`

Batch A, 2026-10-04. Independent refute-first audit; the auditor wrote none of
this code and edited no Lean file. Manifest state is unchanged.

| field | value |
|---|---|
| node id | `thm-brownian-exists` |
| export | `Sandpile.Continuum.exists_isBrownian` |
| file | `Sandpile/Continuum/BrownianExists.lean` |
| state | `SEALED` |
| kind | `theorem` |
| source | the existence of Brownian motion on `ℝ^d` with generator `Δ/(2d)`, proved from the shared library |
| provider | `Sandpile.Continuum.exists_isBrownian` |
| verdict | **PASS** |

## 1. Statement integrity

Frozen block: `theorem Sandpile.Continuum.exists_isBrownian (d : ℕ) : ∃ Ω, … ,
∀ x, IsBrownian d x (B x) P`. The conclusion constructs, on one probability space, a
family of processes `B x` started at each `x`, each with `IsBrownian` (start a.e. at
`x`, each coordinate centred and scaled by `√d` is a real Brownian motion, coordinates
independent). This makes every Brownian-quantified statement non-vacuous. `d = 0` is
included and harmless.

## 2. Proof and axiom closure

The construction builds `d` independent copies of a real Brownian motion, scaled by
`1/√d` and translated by `x`, and verifies start, coordinate law and independence from
`LatticeProb.exists_isBrownianReal`, `isBrownianReal_comp_eval`, `iIndepFun_pi`.
Compiles; `clean thm-brownian-exists`.

## 3. Non-vacuity / junk

Pure existence with an explicit witness (product space `Fin d → Ω₀`, product measure,
`dimBrownian`), so non-vacuous. `IsBrownian` is a substantive three-part predicate; the
independence clause is the nontrivial part and is proved, not assumed.

## 4. Citations

No `External` hypothesis. The node is the explicit discharge of Brownian existence for
the continuum arguments. Genuine.

## Machine evidence

- `lake build Sandpile` → `Build completed successfully (10229 jobs).`
- `python3 tools/check_axioms.py` → `clean thm-brownian-exists`; overall `99 clean, 0 depend
  on sorryAx, 0 unresolved`, `check_axioms: OK (all closures match their
  registered states)`. `#print axioms Sandpile.Continuum.exists_isBrownian` resolves to
  `{propext, Classical.choice, Quot.sound}`.
- `python3 tools/check_manifest.py` → `OK (99 nodes, 0 unsealed)`; the frozen
  block of this node hashes to the manifest `frozen_sha256` and parses as the
  unique declaration `Sandpile.Continuum.exists_isBrownian`.
- `python3 tools/check_warnings.py` → `OK (0 registered sorry warnings)`.
- `python3 tools/check_clauses.py` / `check_exponents.py` / `check_constants.py`
  → `OK` (this node is covered by each).

## Verdict

**PASS.** Statement faithful, proof compiles with the standard axiom closure,
hypotheses satisfiable and conclusion non-junk, citations genuine.
