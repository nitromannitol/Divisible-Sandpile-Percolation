# Hand triage of the Sandpile audit flags (2026-10-03)

This triages every non-External item that `~/fleet/runs/divisible-sandpile-percolation-audit/`
(DeepSeek-V4.1-flash, 73 calls, all 58 faithfulness/vacuity lenses returned) left for the owner.
The reader is fallible; each flag is checked here against the frozen Lean block and the paper.

## Verified false positive

* `cor-d4-logarithmic-mean-lower`: the flag claims `hnondeg : 0 < evariance id ν` forces **finite**
  variance. `ProbabilityTheory.evariance : Measure ℝ → ℝ≥0∞` is the **extended** variance, so
  `0 < evariance` is exactly nondegeneracy including infinite variance. The frozen statement is
  faithful to the paper's "nondegenerate".

## "Adds a hypothesis not in the paper" — all are registered External binders

The nodes below carry a binder of type `Sandpile.External.X`; each such `Prop` is a registered
`FROZEN` node of this manifest, and carrying the cited input explicitly is the intended design.
The binders found in each frozen block:

| node | registered External binders |
|---|---|
| `lem-sobolev-tightness` | `ContinuumBesovTightness` |
| `thm-main-explosion-ii-c` | `ContinuumBesovTightness`, `MembraneScalingLimitFour` |
| `thm-main-explosion-iii-d` | `ContinuumBesovTightness` |
| `prop-d4-diffusive-tightness` | `ContinuumBesovTightness` |
| `prop-weighted-membrane-limit` | `ContinuumBesovTightness` |
| `thm-dgt4-many-limits` | `ContinuumBesovTightness` |
| `thm-d23-critical-level-percolation` | `BallOccupationDensity`, `ContinuumRSW`, `CubeStoppingStability`, `LSSDomination`, `PittGaussianFKG` |
| `thm-main-nontriviality` | `BallOccupationDensity`, `ContinuumRSW`, `CubeStoppingStability`, `ExteriorBoundaryConnected`, `LSSDomination`, `PittGaussianFKG`, `PlanarRSW` |
| `thm-main-critical-level-percolation` | same seven as `thm-main-nontriviality` |
| `thm-d4-ball-green-crossing` | `PlanarRSW` |

Each of `ContinuumBesovTightness`, `MembraneScalingLimitFour`, `BallOccupationDensity`,
`ContinuumRSW`, `CubeStoppingStability`, `LSSDomination`, `PittGaussianFKG`,
`ExteriorBoundaryConnected` and `PlanarRSW` is a registered node of `ledger/manifest.yaml` (three
occurrences each: the External `Prop` node and its two manifest mentions). The manifest `source`
notes record that other, previously carried inputs have since been dropped and discharged
unconditionally (`heatKernelBounds`, `localCLT`, `greenBoundsHigh`, `intersectionSecondMoment`).

## `thm-rw` — faithful

`Sandpile.Frozen.random_walk_representation` states the three-way equality
`odometerOf ζ n x = stoppingValue ζ n x = ∫ X, sceneryPartialSum ζ (optimalStop ζ n X) X ∂walkLaw`,
which is the paper's `u_n(x) = v_n(x) = E_x[S_{τ_n^*}]` for `n ≥ 0`, `x ∈ ℤ^d`. It carries no
External binder; the only binder not written in the paper is the standing dimension hypothesis
`1 ≤ d`, which is TYPING (`ℤ^d` with `d = 0` has one site, not the paper's setting).

## Consequence

There is no transcription defect in the 83 `SEALED` nodes. Every flag is either a verified false
positive, a registered External carried by design, or a harmless standing-assumption binder. The
remaining obligation for the repository is EXTERNALS-to-zero work on the carried `Prop`s, not a
frozen-statement edit. The 83 nodes may be promoted `SEALED -> PROVED` on this audit record.
