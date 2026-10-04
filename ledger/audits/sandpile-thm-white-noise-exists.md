# Audit report — `thm-white-noise-exists`

Batch A, 2026-10-04. Independent refute-first audit; the auditor wrote none of
this code and edited no Lean file. Manifest state is unchanged.

| field | value |
|---|---|
| node id | `thm-white-noise-exists` |
| export | `Sandpile.Continuum.exists_isWhiteNoise` |
| file | `Sandpile/Continuum/WhiteNoiseExists.lean` |
| state | `SEALED` |
| kind | `theorem` |
| source | the existence of white noise on `ℝ^d`, proved from the shared library |
| provider | `Sandpile.Continuum.exists_isWhiteNoise` |
| verdict | **PASS** |

## 1. Statement integrity

Frozen block: `theorem Sandpile.Continuum.exists_isWhiteNoise (d : ℕ) : ∃ Ω, … ,
IsWhiteNoise d W P`. The conclusion is a genuine existential over a probability space
and a family `W`, with `IsWhiteNoise` the four-part predicate (Gaussian, measurable,
centred, covariance = `L²` inner product, plus linearity and joint measurability). The
paper's continuum arguments all quantify over white noise; this node supplies the
witness so they are not vacuous. The statement is `∀ d`, including `d = 0`; that instance
is harmless.

## 2. Proof and axiom closure

The proof constructs the isonormal Gaussian process over a countable orthonormal
basis of `L²(ℝ^d)` (`LatticeProb.l2Basis`, `whiteNoiseOf`, `whiteNoiseLaw`) and checks each
field of `IsWhiteNoise` from the shared library (`isGaussianProcess_whiteNoiseOf`,
`integral_whiteNoiseOf`, `integral_whiteNoiseOf_mul`, `whiteNoiseOf_add`,
`whiteNoiseOf_smul`, `exists_joint_version_of_covariance`). Compiles; `clean
thm-white-noise-exists`.

## 3. Non-vacuity / junk

The statement is a pure existence; the explicit construction is the witness, so it is
non-vacuous by construction. The `IsWhiteNoise` fields are substantive (covariance is
the `L²` inner product, not a junk equality), and the `jointMeas` field quantifies over
strongly measurable `L²` families, so it is not `True`.

## 4. Citations

No `External` hypothesis (none is carried). The node is explicitly the discharge of
the standard existence of white noise, and is stated to prevent vacuity of every
white-noise statement in the repository. Genuine.

## Machine evidence

- `lake build Sandpile` → `Build completed successfully (10229 jobs).`
- `python3 tools/check_axioms.py` → `clean thm-white-noise-exists`; overall `99 clean, 0 depend
  on sorryAx, 0 unresolved`, `check_axioms: OK (all closures match their
  registered states)`. `#print axioms Sandpile.Continuum.exists_isWhiteNoise` resolves to
  `{propext, Classical.choice, Quot.sound}`.
- `python3 tools/check_manifest.py` → `OK (99 nodes, 0 unsealed)`; the frozen
  block of this node hashes to the manifest `frozen_sha256` and parses as the
  unique declaration `Sandpile.Continuum.exists_isWhiteNoise`.
- `python3 tools/check_warnings.py` → `OK (0 registered sorry warnings)`.
- `python3 tools/check_clauses.py` / `check_exponents.py` / `check_constants.py`
  → `OK` (this node is covered by each).

## Verdict

**PASS.** Statement faithful, proof compiles with the standard axiom closure,
hypotheses satisfiable and conclusion non-junk, citations genuine.
