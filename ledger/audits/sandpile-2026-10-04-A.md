# Sandpile seal audit — batch A (`Divisible-Sandpile-Percolation`)

- **Date:** 2026-10-04
- **Auditor:** independent refute-first audit worker. The auditor wrote none of the
  audited Lean code. No Lean file was edited and no manifest state was changed; the
  only writes are the reports in `ledger/audits/`.
- **Repository:** `~/lean/Divisible-Sandpile-Percolation`. Committed `HEAD` when the
  batch was selected was `730c98e`; `git show HEAD:ledger/manifest.yaml` has 83
  `SEALED` and 16 `FROZEN` nodes, matching the brief.
- **Concurrent work (disclosed):** while this audit ran, another fleet worker held
  the working tree and changed `ledger/manifest.yaml` (83 `SEALED` → `PROVED`),
  `CERTIFICATE.md`, `CORRESPONDENCE.md`, `README.md`, `formalization.yaml`,
  `tools/certificate.py`, `tools/freeze.py`, `tools/sync_docs.py`. The auditor made
  none of those edits and changed no manifest state. The node ids and frozen bytes
  are identical between the committed `SEALED` manifest and the working-tree
  `PROVED` manifest; the only difference is the state label. `check_manifest.py` and
  `check_axioms.py` treat `SEALED` and `PROVED` identically (both require a clean
  closure), so the machine evidence below is valid for either label.
- **Batch scope:** 20 `SEALED` leaf nodes (dependency order, providers are cited
  inputs): the 12 `Sandpile/External/*Proved.lean` discharges, the 2
  `Sandpile/Continuum` existence nodes, and 6 foundational `Sandpile/Frozen`
  leaves that have no frozen-node dependency.

## Working-tree manifest state at gate time

The gates below were run against the live working tree, whose `ledger/manifest.yaml`
at that moment had `83 PROVED / 16 FROZEN`. The committed manifest at `HEAD` has
`83 SEALED / 16 FROZEN`. This report names the audited nodes as `SEALED` to match the
brief and the committed contract; no node id, file, export or frozen hash differs
between the two.

| # | node | verdict | statement | proof | non-vacuity | citations |
|---|------|---------|-----------|-------|-------------|-----------|
| 1 | `ext-variance-scale` | **PASS** | OK | OK | OK | OK |
| 2 | `ext-green-bounds-high` | **PASS** | OK | OK | OK | OK |
| 3 | `ext-optimal-stopping` | **PASS** | OK | OK | OK | OK |
| 4 | `thm-gaussian-upper-proved` | **PASS** | OK | OK | OK | OK |
| 5 | `thm-max-displacement-proved` | **PASS** | OK | OK | OK | OK |
| 6 | `ext-heat-kernel-bounds` | **PASS** | OK | OK | OK | OK |
| 7 | `ext-gaussian-law-covariance` | **PASS** | OK | OK | OK | OK |
| 8 | `ext-pinsker` | **PASS** | OK (1 minor citation note) | OK | OK | OK |
| 9 | `ext-local-clt` | **PASS** | OK | OK | OK | OK |
| 10 | `ext-paired-local-clt-four` | **PASS** | OK | OK | OK | OK |
| 11 | `ext-intersection-second-moment` | **PASS** | OK | OK | OK | OK |
| 12 | `ext-ball-green-bounds` | **PASS** | OK | OK | OK | OK |
| 13 | `thm-white-noise-exists` | **PASS** | OK | OK | OK | n/a |
| 14 | `thm-brownian-exists` | **PASS** | OK | OK | OK | n/a |
| 15 | `lem-reflection-increment` | **PASS** | OK (fidelity note) | OK | OK | OK |
| 16 | `lem-weighted-exp-conc` | **PASS** | OK | OK | OK | OK |
| 17 | `lem-convex-linear-bound` | **PASS** | OK | OK | OK (junk-guard observed) | OK |
| 18 | `lem-recursion` | **PASS** | OK | OK | OK | OK |
| 19 | `prop-finite-time-concentration-scale` | **PASS** | OK | OK | OK | OK |
| 20 | `lem-d4-double-heat-kernel` | **PASS** | OK (stronger than paper, stale review note) | OK | OK | OK |

**20 PASS / 0 FAIL.** Two notes of record (neither refutes a node): a wrong
`source` line number in `ext-pinsker`, and a stale `check_clauses.py` review
record for `lem-d4-double-heat-kernel`. Neither is a defect in the Lean
statement or proof.

## Gate commands and exact output

All commands were run in `~/lean/Divisible-Sandpile-Percolation` on 2026-10-04.

```
$ lake build Sandpile
...
Build completed successfully (10229 jobs).

$ python3 tools/check_manifest.py
check_manifest: OK (99 nodes, 0 unsealed; closure 0 checked, 99 skipped; 746 Sandpile declarations indexed)

$ python3 tools/check_axioms.py
  clean   ext-variance-scale
  ...
  clean   lem-brownian-ball-localization

99 clean, 0 depend on sorryAx, 0 unresolved
check_axioms: OK (all closures match their registered states)

$ python3 tools/check_warnings.py
check_warnings: OK (0 registered sorry warnings)

$ python3 tools/check_coverage.py
check_coverage: 58 statements in the paper, 58 represented in the manifest
every theorem, lemma, proposition and corollary has a manifest entry

$ python3 tools/check_clauses.py
check_clauses: OK (69 statements, each read against the paper and its correspondence recorded; 40 where the count heuristic says the paper asserts more, all explained above)

$ python3 tools/check_exponents.py
check_exponents: OK (81 statements; every paper exponent appears in its Lean statement or is explained above)

$ python3 tools/check_constants.py
check_constants: OK (99 statements; every existential constant is bound before every paper parameter, so it is a genuine constant)

$ python3 tools/check_progress.py
check_progress: OK (0 -> 0 open hole(s))
```

`check_axioms.py` used `#print axioms` on all 99 manifest exports through a
single scratch module; each export resolved exactly once and every closure was
`{propext, Classical.choice, Quot.sound}`. For all 20 batch nodes the output line
is `clean <node-id>`.

A second, targeted probe (`lake env lean` on a file importing only the 20 batch
modules, run 2026-10-04) printed the exact closure of each export:

```
'Sandpile.External.varianceScale'                    depends on axioms: [propext, Classical.choice, Quot.sound]
'Sandpile.External.greenBoundsHigh'                  depends on axioms: [propext, Classical.choice, Quot.sound]
'Sandpile.External.optimalStopping'                  depends on axioms: [propext, Classical.choice, Quot.sound]
'Sandpile.External.gaussianUpper'                    depends on axioms: [propext, Classical.choice, Quot.sound]
'Sandpile.External.maxDisplacement'                  depends on axioms: [propext, Classical.choice, Quot.sound]
'Sandpile.External.heatKernelBounds'                 depends on axioms: [propext, Classical.choice, Quot.sound]
'Sandpile.External.gaussianLawDeterminedByCovariance' depends on axioms: [propext, Classical.choice, Quot.sound]
'Sandpile.External.pinsker'                          depends on axioms: [propext, Classical.choice, Quot.sound]
'Sandpile.External.localCLT'                         depends on axioms: [propext, Classical.choice, Quot.sound]
'Sandpile.External.pairedLocalCLTFour'               depends on axioms: [propext, Classical.choice, Quot.sound]
'Sandpile.External.intersectionSecondMoment'         depends on axioms: [propext, Classical.choice, Quot.sound]
'Sandpile.External.ballGreenBounds'                  depends on axioms: [propext, Classical.choice, Quot.sound]
'Sandpile.Continuum.exists_isWhiteNoise'             depends on axioms: [propext, Classical.choice, Quot.sound]
'Sandpile.Continuum.exists_isBrownian'               depends on axioms: [propext, Classical.choice, Quot.sound]
'Sandpile.Frozen.reflection_increment'               depends on axioms: [propext, Classical.choice, Quot.sound]
'Sandpile.Frozen.weighted_exp_concentration'         depends on axioms: [propext, Classical.choice, Quot.sound]
'Sandpile.Frozen.convex_linear_bound'                depends on axioms: [propext, Classical.choice, Quot.sound]
'Sandpile.Frozen.odometer_recursion'                 depends on axioms: [propext, Classical.choice, Quot.sound]
'Sandpile.Frozen.finite_time_concentration_scale'    depends on axioms: [propext, Classical.choice, Quot.sound]
'Sandpile.Frozen.d4_double_heat_kernel'              depends on axioms: [propext, Classical.choice, Quot.sound]
```

Each closure is **exactly** the three standard axioms, as required.

### Build reproducibility note

The first `lake build Sandpile` (log `/tmp/sandpile_build.log`) reported eight
targets with `no such file or directory (error code: 4294967294)` and
`error: build failed`. Every failing target was an `.olean` write/read race
under concurrent fleet-wide activity on the shared store (other agents were
holding `/home/bourabbe/.lake-global.lock` and running `lake` in the same
working tree). All eight `.olean` files were present immediately afterwards. A
re-run of `lake build Sandpile` completed successfully with **10229 jobs** and
exit code 0, and `check_warnings.py`, `check_axioms.py` and the remaining gates
all pass on that build. There is no source-level compile error.

## Findings of record

### N-1 (minor, citation metadata) — `ext-pinsker` source line number

`ledger/manifest.yaml` and `Sandpile/External/Pinsker.lean` both cite
`sandpile.tex:2390` for Pinsker's inequality. The sentence that invokes it
("Since `𝔗_M` determines `E_R(θ)`, Pinsker's inequality gives …") is at
`sandpile.tex:2422`; line 2390 is inside the revealed-cubes bookkeeping with no
inequality. The citation is genuine (Pinsker's inequality is exactly what
`ext-pinsker` states and proves), only the line anchor is off by 32 lines. Not
a statement or proof defect.

### N-2 (minor, tool state) — stale `check_clauses.py` review for `lem-d4-double-heat-kernel`

The `REVIEWED` entry for `lem-d4-double-heat-kernel` in `tools/check_clauses.py`
still says the frozen statement carries `hLocalCLT : External.LocalCLT` and that
"hLocalCLT is not used in the Lean proof (bound to an unused name)". The current
frozen statement in `Sandpile/Frozen/DoubleHeatKernel.lean` binds **only**
`hPaired : Sandpile.External.PairedLocalCLTFour`, imports
`Sandpile.External.LocalCLT`, and the manifest `source` records that the local
CLT hypothesis was dropped and is discharged unconditionally. The Lean node is
therefore strictly **stronger** than the stale review describes; the node is
PASS. The stale sentence should be refreshed in the tool.

### Observed, not a defect — `lem-convex-linear-bound` junk-guard

The proof of `lem-convex-linear-bound` splits on
`Integrable (fun ξ => (F ξ - c - Σ a_i ξ_i)^2) π`. In the non-integrable branch it
rewrites the Bochner integral to `0` (`integral_undef`) and uses only that the
right-hand side is non-negative. Under the paper's hypotheses the integrand is
in fact integrable (coordinatewise convexity plus `0 ≤ ∂_i⁺F ≤ b_i` makes `F`
Lipschitz in each coordinate, hence at most linear growth against a finite
second moment), so the branch is unreachable on the paper's instances and the
statement is not vacuous; the guard is a sound way to avoid reading a junk
value. Recorded for transparency, not counted as a defect.

### Statement-integrity method

Each node's frozen block was read byte-for-byte from its file (hashes confirmed
by `check_manifest.py`) and compared with the cited `sandpile.tex` lines or with
the cited external statement. The pre-existing `check_clauses.py` readings were
treated as claims to verify, not as evidence; the two places where the current
bytes differ from that reading are recorded above. Exponents were checked
against `check_exponents.py` and the paper displays; the constant-order gate
`check_constants.py` confirms every existential constant is bound before `β`,
`n`, `k`, `m`, `h`, so no constant silently absorbs a paper parameter.
