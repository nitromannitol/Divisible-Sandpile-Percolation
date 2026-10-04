# Audit report — `lem-d4-double-heat-kernel`

Batch A, 2026-10-04. Independent refute-first audit; the auditor wrote none of
this code and edited no Lean file. Manifest state is unchanged.

| field | value |
|---|---|
| node id | `lem-d4-double-heat-kernel` |
| export | `Sandpile.Frozen.d4_double_heat_kernel` |
| file | `Sandpile/Frozen/DoubleHeatKernel.lean` |
| state | `SEALED` |
| kind | `theorem` |
| source | sandpile.tex:1164-1169 (label `lem:d4-double-heat-kernel`); the local CLT hypothesis is dropped, discharged by `Sandpile.External.localCLT` |
| provider | `Sandpile.Frozen.d4_double_heat_kernel` |
| verdict | **PASS** |

## 1. Statement integrity

Frozen block: `theorem Sandpile.Frozen.d4_double_heat_kernel
(hPaired : Sandpile.External.PairedLocalCLTFour) : ∃ C, ∀ t ≥ 2, ∀ x y,
sqDist x y ≤ t → |(∑_{a<t}∑_{b<t} p_{a+b}(x,y)) - (4/π²) log(t/(1+sqDist x y))| ≤ C`.
This is the paper's `lem:d4-double-heat-kernel`, with the paper's "uniformly" written as
a single constant `C` bound before `t, x, y`, the double sum as nested `Finset.range t`
sums, `|x-y|²` as the integer coordinate sum `sqDist`, and `2 ≤ t`, `sqDist ≤ t` keeping
the logarithm's argument positive. The manifest source records that the local CLT
hypothesis was **dropped** (discharged by `Sandpile.External.localCLT`); the Lean is
therefore **stronger** than the paper, which is a fidelity note, not a defect.
**Tool note N-2:** the `check_clauses.py` `REVIEWED` text for this node is stale and
still lists an unused `hLocalCLT`; the current bytes carry only `hPaired`.

## 2. Proof and axiom closure

The proof is the one-line application `simpa only [Sandpile.sqDist] using
Sandpile.exists_double_heat_kernel_four_bound hPaired`. Compiles; `clean
lem-d4-double-heat-kernel`.

## 3. Non-vacuity / junk

`2 ≤ t` and `sqDist x y ≤ t` are satisfiable; `C` can be taken large. The left side
is a genuine finite double sum of heat kernels (each finitely supported) and the
logarithm's argument `t/(1+|x-y|²)` is positive under `2 ≤ t` and `|x-y|² ≤ t`, so no
`Real.log 0` junk. The `O(1)` is an honest absolute-value bound.

## 4. Citations

The node carries one `External` hypothesis, `PairedLocalCLTFour`, which is a genuine
cited input (Lawler-Limic Theorem 2.1.3 Eq. (2.8)) and is itself proved by
`Sandpile/External/PairedLocalCLTFourProved.lean` (node `ext-paired-local-clt-four`,
audited here as PASS). The `LocalCLT` hypothesis has been dropped and is discharged by
`Sandpile.External.localCLT` (node `ext-local-clt`, PASS). Citation requirement met.

## Machine evidence

- `lake build Sandpile` → `Build completed successfully (10229 jobs).`
- `python3 tools/check_axioms.py` → `clean lem-d4-double-heat-kernel`; overall `99 clean, 0 depend
  on sorryAx, 0 unresolved`, `check_axioms: OK (all closures match their
  registered states)`. `#print axioms Sandpile.Frozen.d4_double_heat_kernel` resolves to
  `{propext, Classical.choice, Quot.sound}`.
- `python3 tools/check_manifest.py` → `OK (99 nodes, 0 unsealed)`; the frozen
  block of this node hashes to the manifest `frozen_sha256` and parses as the
  unique declaration `Sandpile.Frozen.d4_double_heat_kernel`.
- `python3 tools/check_warnings.py` → `OK (0 registered sorry warnings)`.
- `python3 tools/check_clauses.py` / `check_exponents.py` / `check_constants.py`
  → `OK` (this node is covered by each).

## Verdict

**PASS.** Statement faithful, proof compiles with the standard axiom closure,
hypotheses satisfiable and conclusion non-junk, citations genuine.
