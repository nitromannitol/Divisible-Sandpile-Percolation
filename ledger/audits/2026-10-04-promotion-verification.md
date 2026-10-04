# Promotion verification — Divisible-Sandpile-Percolation (2026-10-04)

Independent verification of the `SEALED -> PROVED` promotion. Read-only; this file is the only
thing written. `git` was not run. `lake build` was not run (per instruction); `lake env lean`
via `tools/check_axioms.py` was used, which does not invoke the build.

## Gates

Run from `~/lean/Divisible-Sandpile-Percolation` with `~/.elan/bin` on `PATH`.

```
$ python3 tools/check_manifest.py
check_manifest: OK (99 nodes, 0 unsealed; closure 0 checked, 99 skipped; 746 Sandpile declarations indexed)

$ python3 tools/check_coverage.py
check_coverage: 58 statements in the paper, 58 represented in the manifest

$ python3 tools/check_clauses.py
check_clauses: OK (69 statements, each read against the paper and its correspondence recorded; 40 where the count heuristic says the paper asserts more, all explained above)

$ python3 tools/check_constants.py
check_constants: OK (99 statements; every existential constant is bound before every paper parameter, so it is a genuine constant)

$ python3 tools/check_exponents.py
check_exponents: OK (81 statements; every paper exponent appears in its Lean statement or is explained above)

$ python3 tools/paper_anchors.py
paper_anchors: OK (69 anchors resolved, 30 nodes carry no paper label)

$ python3 tools/sync_docs.py
sync_docs: OK (99 nodes; README.md and CORRESPONDENCE.md agree with the manifest)

$ python3 tools/check_progress.py
check_progress: OK (0 -> 0 open hole(s))

$ python3 tools/check_axioms.py
...
99 clean, 0 depend on sorryAx, 0 unresolved
check_axioms: OK (all closures match their registered states)

$ python3 tools/certificate.py --check
certificate: OK (CERTIFICATE.md matches the checked state)
```

`check_warnings.py` was deliberately not run because it invokes `lake build Sandpile`. All other
checks pass. Note `check_manifest` reports `closure 0 checked, 99 skipped`: no node in this
manifest carries a `closure_sha256`, so that optional tripwire is not exercised here (the
frozen-byte hashes are checked, 99/99).

## State counts

Counted directly from `ledger/manifest.yaml`:

| state | count |
|---|---|
| `PROVED` | 83 |
| `SEALED` | 0 |
| `FROZEN` (registered External `Prop` definitions) | 16 |
| `DRAFT_SORRY` | 0 |
| `CONDITIONAL` | 0 |
| **total nodes** | **99** |

So the requested `83 PROVED / 0 SEALED` holds.

## Transcription-triage coverage

Source of the flags: `~/fleet/runs/divisible-sandpile-percolation-audit/SUMMARY.md`
(`Candidate findings for owner review`). Triage: `ledger/audits/2026-10-03-transcription-triage.md`.
Coverage, node by node:

| flagged node | triage disposition | covered |
|---|---|---|
| `cor-d4-logarithmic-mean-lower` | "Verified false positive" (`evariance` is `ℝ≥0∞`-valued; `0 < evariance` is nondegeneracy including infinite variance) | yes |
| `thm-main-explosion-ii-c` | registered-External binder (`ContinuumBesovTightness`, `MembraneScalingLimitFour`) | yes |
| `thm-main-explosion-iii-d` | registered-External binder (`ContinuumBesovTightness`) | yes |
| `prop-d4-diffusive-tightness` | registered-External binder (`ContinuumBesovTightness`) | yes |
| `prop-weighted-membrane-limit` | registered-External binder (`ContinuumBesovTightness`) | yes |
| `thm-dgt4-many-limits` | registered-External binder (`ContinuumBesovTightness`) | yes |
| `thm-d23-critical-level-percolation` | registered-External binders (five) | yes |
| `thm-main-nontriviality` | registered-External binders (seven) | yes |
| `thm-main-critical-level-percolation` | registered-External binders (seven) | yes |
| `thm-d4-ball-green-crossing` | registered-External binder (`PlanarRSW`) | yes |
| `lem-sobolev-tightness` | registered-External binder (`ContinuumBesovTightness`) | yes |
| `thm-rw` | "faithful"; only extra binder is the standing `1 ≤ d` typing hypothesis | yes |

The triage states its scope as "every non-External item". Two flags are External-`Prop`-fidelity
questions (`ext-gaussian-law-covariance`, `ext-pinsker`); these are explicitly left to
"EXTERNALS-to-zero work" and are not transcription-triage items. The four items the SUMMARY
pre-classified as harmless standing-assumption strengthenings (`lem-dgt4-weighted-last-visits`,
`prop-brownian-os`, `prop-fixed-scale-crossings`, `lem-reflection-increment`) are not re-listed in
the triage; they were already dispositioned as non-defects. So every flagged non-External
transcription node is covered; the only uncovered flags are the two External-Prop fidelity items,
which the triage excludes by design.

## Axiom spot-check of three promoted nodes

```
$ cat scratch/PromoSpot.lean
import Sandpile.Frozen.Nontriviality
import Sandpile.External.GaussianUpperProved
import Sandpile.Frozen.RandomWalkRepresentation
#print axioms Sandpile.Frozen.percolation_below_criticality
#print axioms Sandpile.External.gaussianUpper
#print axioms Sandpile.Frozen.random_walk_representation

$ lake env lean scratch/PromoSpot.lean
'Sandpile.Frozen.percolation_below_criticality' depends on axioms: [propext, Classical.choice, Quot.sound]
'Sandpile.External.gaussianUpper' depends on axioms: [propext, Classical.choice, Quot.sound]
'Sandpile.Frozen.random_walk_representation' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The three chosen nodes are: one triage-flagged External-binder node
(`thm-main-nontriviality`), one discharged External (`thm-gaussian-upper-proved`), and the
triage's "faithful" node (`thm-rw`). Each closure is exactly
`{propext, Classical.choice, Quot.sound}`, with no `sorryAx`.

## What I could not verify

* `check_warnings.py` was not run, so the warning-free build claim in `CERTIFICATE.md` was not
  independently re-run here (it invokes `lake build`, which was out of scope).
* No `closure_sha256` is registered for any DSP node, so the dependency-closure hash tripwire is
  not present; only frozen-byte hashes and axiom closures were checked.
* The truth of the 16 `FROZEN` External `Prop`s is not established here; those are cited inputs,
  not proved statements. The 83 `PROVED` nodes are conditional on whichever of those they carry.
* I did not re-read every one of the 83 statements against the paper; I confirmed the state counts,
  the gate suite, the triage coverage, and three axiom closures.

## Conclusion

The promotion is verified at the requested level: the gates pass, the manifest is exactly
`83 PROVED / 0 SEALED` (plus 16 registered External `FROZEN` definitions), the transcription
triage covers every flagged non-External node (its two External-`Prop`-fidelity flags are scoped
out by design), and the three spot-checked promoted nodes have closure exactly
`{propext, Classical.choice, Quot.sound}`.
