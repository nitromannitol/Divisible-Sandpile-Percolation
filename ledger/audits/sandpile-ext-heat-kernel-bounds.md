# Audit report — `ext-heat-kernel-bounds`

Batch A, 2026-10-04. Independent refute-first audit; the auditor wrote none of
this code and edited no Lean file. Manifest state is unchanged.

| field | value |
|---|---|
| node id | `ext-heat-kernel-bounds` |
| export | `Sandpile.External.heatKernelBounds` |
| file | `Sandpile/External/HeatKernelBoundsProved.lean` |
| state | `SEALED` |
| kind | `theorem` |
| source | external input: Lawler-Limic Propositions 2.4.1 and 2.4.4 with Hoeffding, the estimates of `ssec:green-estimates` |
| provider | `Sandpile.External.heatKernelBounds` |
| verdict | **PASS** |

## 1. Statement integrity

Frozen block: `theorem Sandpile.External.heatKernelBounds : Sandpile.External.HeatKernelBounds`.
`HeatKernelBounds` (frozen in `Sandpile/External/HeatKernelBounds.lean`) is the
three-conjunct transcription of `eq:rw-gaussian-upper`, `eq:rw-tv-gradient` and
`eq:rw-max-displacement`: the Gaussian upper bound, the total-variation gradient bound
for same-parity sites (`SameParity x w`), and the maximal-displacement tail. Each
conjunct binds its positive constants before the parameters and the tail bound uses
`ENNReal.ofReal`. Quantifier order and constants match the paper.

## 2. Proof and axiom closure

The proof is a one-line tuple application of the two `*Proved` nodes
`Sandpile.External.gaussianUpper` and `Sandpile.External.maxDisplacement` together with
the registered provider `Sandpile.exists_heatKernel_tv_gradient`. This is a short chain
within the batch. Compiles; `clean ext-heat-kernel-bounds`.

## 3. Non-vacuity / junk

`1 ≤ d` is satisfiable. The three conjuncts are the paper's displays with positive
constants and honest `ENNReal.ofReal` bounds; the gradient clause quantifies over
same-parity pairs, so it is not an empty statement, and the heat kernel is finitely
supported so the `tsum` there is finite. No junk value.

## 4. Citations

Two of the three ingredients are themselves batch nodes with `...Proved.lean`
discharges; `exists_heatKernel_tv_gradient` is a library theorem. No assumed `External`
is left. Genuine.

## Machine evidence

- `lake build Sandpile` → `Build completed successfully (10229 jobs).`
- `python3 tools/check_axioms.py` → `clean ext-heat-kernel-bounds`; overall `99 clean, 0 depend
  on sorryAx, 0 unresolved`, `check_axioms: OK (all closures match their
  registered states)`. `#print axioms Sandpile.External.heatKernelBounds` resolves to
  `{propext, Classical.choice, Quot.sound}`.
- `python3 tools/check_manifest.py` → `OK (99 nodes, 0 unsealed)`; the frozen
  block of this node hashes to the manifest `frozen_sha256` and parses as the
  unique declaration `Sandpile.External.heatKernelBounds`.
- `python3 tools/check_warnings.py` → `OK (0 registered sorry warnings)`.
- `python3 tools/check_clauses.py` / `check_exponents.py` / `check_constants.py`
  → `OK` (this node is covered by each).

## Verdict

**PASS.** Statement faithful, proof compiles with the standard axiom closure,
hypotheses satisfiable and conclusion non-junk, citations genuine.
