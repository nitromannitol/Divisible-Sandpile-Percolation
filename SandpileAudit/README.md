# SandpileAudit Comparator Surface

This directory contains Mathlib-only comparator challenges for the main theorems
of the formalization of *Quantitative explosion and percolation of the divisible
sandpile* (Bou-Rabee and Panagiotis, arXiv:2609.02829): Theorem 1.1 on
percolation of the toppled set below mean one, Theorem 1.2 on percolation of the
critical level sets, and the ten parts of Theorem 1.3 on critical growth and
spatial scaling, each registered as its own node.  Each comparator lives in its
own subdirectory:

| Directory | Paper statement | Checked theorem | Library theorem |
| --- | --- | --- | --- |
| `Nontriviality/` | Theorem 1.1, `thm:main-nontriviality` | `SandpileAudit.percolation_below_criticality` | `Sandpile.percolation_below_criticality` |
| `CriticalLevels/` | Theorem 1.2, `thm:main-critical-level-percolation` | `SandpileAudit.critical_level_percolation` | `Sandpile.critical_level_percolation` |
| `MeanGrowthLow/` | Theorem 1.3(i)(a), `thm:main-explosion` | `SandpileAudit.mean_growth_le_three` | `Sandpile.mean_growth_le_three` |
| `BrownianScalingLimit/` | Theorem 1.3(i)(b), `thm:main-explosion` | `SandpileAudit.brownian_scaling_limit` | `Sandpile.brownian_scaling_limit` |
| `MeanGrowthFour/` | Theorem 1.3(ii)(a), first clause, `thm:main-explosion` | `SandpileAudit.mean_growth_four` | `Sandpile.mean_growth_four` |
| `FourFirstOrder/` | Theorem 1.3(ii)(a), second clause, `thm:main-explosion` | `SandpileAudit.four_first_order` | `Sandpile.four_first_order` |
| `FourGaussian/` | Theorem 1.3(ii)(b), `thm:main-explosion` | `SandpileAudit.four_gaussian` | `Sandpile.four_gaussian` |
| `FourSobolev/` | Theorem 1.3(ii)(c), `thm:main-explosion` | `SandpileAudit.four_sobolev` | `Sandpile.four_sobolev` |
| `HighFirstOrder/` | Theorem 1.3(iii)(a), `thm:main-explosion` | `SandpileAudit.high_first_order` | `Sandpile.high_first_order` |
| `HighTail/` | Theorem 1.3(iii)(b), `thm:main-explosion` | `SandpileAudit.high_tail` | `Sandpile.high_tail` |
| `HighSobolevLimit/` | Theorem 1.3(iii)(c), `thm:main-explosion` | `SandpileAudit.high_sobolev_limit` | `Sandpile.high_sobolev_limit` |
| `HighNonconvergence/` | Theorem 1.3(iii)(d), `thm:main-explosion` | `SandpileAudit.high_nonconvergence` | `Sandpile.high_nonconvergence` |

Each `Challenge.lean` imports only `Mathlib`, rebuilds from scratch every
definition needed to read the theorem, states the theorem, and ends with one
`sorry`, the proof being checked.  The definitions form one vocabulary block,
between `-- VOCABULARY-BEGIN` and `-- VOCABULARY-END`, byte-identical in all
twelve challenges: lattice sites, the nearest-neighbour lattice, i.i.d. laws, the
simple random walk heat kernel and the Brownian exit time (from
`Lattice-Probability`); the odometer, its limit and the toppled set, the mass
laws, the Green kernels, the walk on path space and its stopping problems, the
scenery and the membrane field; the Brownian heat and Green kernels, test
functions, negative Sobolev norms, the lattice pairing, the membrane covariances,
white noise, Brownian motion, the Brownian stopping values and the multilinear
interpolation; the planar crossing events, the `∗`-lattice and the exterior
boundary, the continuum planar fields and their crossings; and the cited
results that the twelve statements carry as hypotheses (thirteen of them; see
"What Is Checked").  The vocabulary also defines six cited results that no
statement below takes as a hypothesis, since each is proved unconditionally in
the repository (`GreenBoundsHigh`, `HeatKernelBounds`, `VarianceScale`,
`LocalCLT`, `PairedLocalCLTFour`, `BallGreenBounds`); a seventh,
`IntersectionSecondMoment`, is likewise proved unconditionally and is not
defined in the vocabulary at all.

## What Is Checked

The theorems are conditional on results the paper cites without proof, and so
are the challenges: each carries, as explicit hypotheses, the cited results its
library theorem carries, restated in the vocabulary.

| Directory | Cited results carried as hypotheses (namespace `External`) |
| --- | --- |
| `Nontriviality/` | `PlanarRSW`, `LSSDomination`, `ExteriorBoundaryConnected`, `ContinuumRSW`, `PittGaussianFKG`, `BallOccupationDensity`, `CubeStoppingStability` |
| `CriticalLevels/` | `PlanarRSW`, `LSSDomination`, `ExteriorBoundaryConnected`, `ContinuumRSW`, `PittGaussianFKG`, `BallOccupationDensity`, `CubeStoppingStability` |
| `MeanGrowthLow/` | `ContinuumStoppingStability`, `ContinuumOptimalStopping` |
| `BrownianScalingLimit/` | `ContinuumStoppingStability` |
| `MeanGrowthFour/` | none |
| `FourFirstOrder/` | none |
| `FourGaussian/` | none |
| `FourSobolev/` | `ContinuumBesovTightness`, `MembraneScalingLimitFour` |
| `HighFirstOrder/` | none |
| `HighTail/` | none |
| `HighSobolevLimit/` | `GaussianLipschitzConcentration`, `NormalComparison`, `ContinuumBesovTightness` |
| `HighNonconvergence/` | `ContinuumBesovTightness` |

Seven cited results, `GreenBoundsHigh`, `HeatKernelBounds`, `VarianceScale`,
`IntersectionSecondMoment`, `LocalCLT`, `PairedLocalCLTFour` and
`BallGreenBounds`, are proved unconditionally in the repository
(`Sandpile/External/*Proved.lean`; see `ASSUMPTIONS.md`) rather than assumed;
none of the twelve certified statements, and so none of the challenges above,
carries any of the seven as a hypothesis.

The content of each theorem is summarized in the docstring of its challenge and
in `Sandpile/MainTheorems.lean`.

## Definition Provenance

The challenge definitions are statement-level copies of the definitions the
repository uses to state the theorems, in the namespace `SandpileAudit`.  A
library or repository name `LatticeProb.X`, `Sandpile.X`,
`Sandpile.Continuum.X` or `Sandpile.External.X` becomes `SandpileAudit.X`,
`SandpileAudit.Continuum.X` or `SandpileAudit.External.X`.

| Challenge declaration | Source |
| --- | --- |
| `Site`, `unit`, `lattice`, `nbrSum`, `walkOp`, `componentIn`, `HasInfiniteComponent` | `LatticeProb/Site.lean` (Lattice-Probability), re-exported as `Sandpile.Site` and so on |
| `iidLaw`, `instructionLaw` | `LatticeProb/IID.lean` |
| `heatKernel` | `LatticeProb/Walk/LocalCLT.lean` (`LatticeProb.LocalCLT.heatKernel`, named `Sandpile.heatKernel` by an abbreviation) |
| `greenTime` | `LatticeProb/Walk/LatticeGreen.lean` (named `Sandpile.greenTime` by an abbreviation) |
| `gaussLaw` | `LatticeProb/Gauss/Coords.lean` |
| `exitTime` | `LatticeProb/Prob/BrownianExitTime.lean` |
| `relax`, `odometer`, `odometerLimit`, `toppledSet`, `massLaw` | `Sandpile/Basic.lean` |
| `centeredMassLaw`, `meanOdometer` and the two probability-measure instances | `Sandpile/Law.lean` |
| `green`, `killedKernel`, `killedGreenTime`, `killedGreen`, `stepLaw`, `walkPath`, `walkLaw`, `IsWalkStopping`, `stoppingSup`, `scenery`, `avg`, `membrane` | `Sandpile/Walk.lean` |
| `criticalScale` | `Sandpile/Support/Crit23Scale.lean` |
| `supBox` | `Sandpile/Frozen/MeanLocalization.lean` (a definition outside the frozen block) |
| `killedSet`, `killedStoppingSup` | `Sandpile/Support/KillRep.lean` |
| `potentialKernel` | `Sandpile/Support/D4PotentialKernel.lean` |
| `Continuum.Space`, `heatKernelBM`, `greenTimeBM` | `Sandpile/Continuum/Kernel.lean` |
| `Continuum.IsTestFn`, `sobolevNormSq`, `negSobolevNorm`, `embed`, `latticePairing`, `IsDomain` | `Sandpile/Continuum/Sobolev.lean` |
| `Continuum.weightedMembraneCov`, `membraneCov4`, `omegaRep`, `IsAveragingDensity`, `TightInNegSobolev`, `TendstoInNegSobolev`, and `omegaMembraneCov4` | `Sandpile/Continuum/Membrane.lean` |
| `Continuum.IsWhiteNoise`, `gaussianPotential` | `Sandpile/Continuum/WhiteNoise.lean` |
| `Continuum.IsBrownian`, `brownianFiltration`, `IsBrownianStopping`, `brownianDiscount`, `brownianValue` | `Sandpile/Continuum/Stopping.lean` |
| `Continuum.cubeStoppingPayoffs`, `brownianDiscountCube` | `Sandpile/Support/ExplKilledValue.lean` |
| `Continuum.multilinearInterp` | `Sandpile/Support/ExplInterp.lean` |
| `Continuum.diffusiveFluctuation` | `Sandpile/Support/ExplFluctuation.lean` |
| `planarFieldShift`, `planarFieldTranspose`, `planarFieldReflect`, `IsSymmetricPlanarLaw`, `IsAssociatedPlanarLaw`, `planarCrossingEvent`, `probabilityInUnitInterval` | `Sandpile/Support/PlanarLaw.lean` |
| `planeRectangle` | `Sandpile/Support/PlaneRectangle.lean` |
| `IsCrossingPath`, `crossingValue` | `Sandpile/Support/CrossingDefinitions.lean` |
| `starLattice` | `Sandpile/Frozen/DGT4LevelShiftDecoupling.lean` (a definition outside the frozen block) |
| `starLatticeGraph` | `Sandpile/Support/StarCrossings.lean` |
| `exteriorVertexBoundary` | `Sandpile/Support/ExteriorBoundary.lean` |
| `Continuum.PlaneSymmetry`, `PlaneSymmetry.toFun`, `fieldLaw`, `IsSymmetricField`, `IsAssociatedField` | `Sandpile/Support/CrossField.lean` |
| `FixedScaleCrossings.planePoint`, `ballKernel`, `rectSet`, `Crosses` | `Sandpile/Support/ContinuumPlanar.lean` (namespace `Sandpile.Frozen.FixedScaleCrossings`) |
| `External.*` and their auxiliary definitions (`BallGreen.*`, `Variance.*`, `Lclt.*`, `Snell.*`, `latticeNorm`, `latticeDist`, `tailKernel`, `SameParity`, `membraneDefect`) | `Sandpile/External/` |

The only textual changes are the namespaces, a proof of the irreflexivity field
of `lattice` that uses no library lemma, and the `noncomputable` marker on
`planeRectangle`, which the repository gets from a `noncomputable section`.

## Solutions

Each pair has four files: `Challenge.lean`, `SolutionBasic.lean`, `Solution.lean` and
`comparator.json`.  `SolutionBasic.lean` is a verbatim, mechanical copy of the vocabulary block
of the pair's `Challenge.lean`, and imports only Mathlib.  `Solution.lean` imports the
repository together with the pair's `SolutionBasic.lean` and its bridge
`SandpileAudit/Support/<Pair>Bridge.lean`, and proves the byte-identical statement from the
corresponding theorem of `Sandpile/MainTheorems.lean` (see [`DESIGN.md`](DESIGN.md)).  The
comparator checks each solution statement against its challenge, and the dependency closure
against Mathlib.

## Reproducing The Checks

The comparator configurations permit only

```json
["propext", "Quot.sound", "Classical.choice"]
```

and enable the nanoda replay.  Each challenge elaborates standalone against
this repository's Mathlib toolchain, e.g.

```bash
bash SandpileAudit/check_standalone.sh SandpileAudit/Nontriviality/Challenge.lean
bash SandpileAudit/check_standalone.sh --vocabulary
```

with expected outcome `rc=0` and exactly one `declaration uses 'sorry'`
warning per challenge; the second command checks that the vocabulary block of
each challenge is byte-identical to that of its `SolutionBasic.lean`.  The
solutions build with

```bash
lake build SandpileAudit
```

Then, with `leanprover/comparator`, `lean4export` (at the toolchain's tag), `landrun` and
`nanoda` built at the pins of [`COMPARATOR_RUNS.md`](COMPARATOR_RUNS.md), from the repository
root:

```bash
COMPARATOR_LANDRUN=<landrun> COMPARATOR_LEAN4EXPORT=<lean4export> COMPARATOR_NANODA=<nanoda_bin> \
  lake env <comparator>/.lake/build/bin/comparator SandpileAudit/<Pair>/comparator.json
```

**Status.**  All twelve solutions build.  `leanprover/comparator` passes on all twelve pairs,
with the Lean kernel and again with the independent nanoda kernel.
[`COMPARATOR_RUNS.md`](COMPARATOR_RUNS.md) records the pins, the results and
the reproduction steps.  The workflow
[`.github/workflows/comparator.yml`](../.github/workflows/comparator.yml) runs
it on request.
