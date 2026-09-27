# Audit Comparator Surface

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
results that the twelve statements carry: seventeen are still carried as
hypotheses, and three more (`GreenBoundsHigh`, `HeatKernelBounds`,
`VarianceScale`) the vocabulary still defines but no statement below takes as a
hypothesis, since each is proved unconditionally in the repository; see "What
Is Checked".

## What Is Checked

The theorems are conditional on results the paper cites without proof, and so
are the challenges: each carries, as explicit hypotheses, the cited results its
library theorem carries, restated in the vocabulary.

| Directory | Cited results carried as hypotheses (namespace `External`) |
| --- | --- |
| `Nontriviality/` | `BallGreenBounds`, `PlanarRSW`, `LSSDomination`, `ExteriorBoundaryConnected`, `ContinuumRSW`, `PittGaussianFKG`, `BallOccupationDensity`, `LocalCLT`, `CubeStoppingStability` |
| `CriticalLevels/` | `BallGreenBounds`, `PlanarRSW`, `LSSDomination`, `ExteriorBoundaryConnected`, `ContinuumRSW`, `PittGaussianFKG`, `BallOccupationDensity`, `LocalCLT`, `CubeStoppingStability` |
| `MeanGrowthLow/` | `LocalCLT`, `ContinuumStoppingStability`, `ContinuumOptimalStopping` |
| `BrownianScalingLimit/` | `LocalCLT`, `ContinuumStoppingStability` |
| `MeanGrowthFour/` | none |
| `FourFirstOrder/` | none |
| `FourGaussian/` | `PairedLocalCLTFour` |
| `FourSobolev/` | `ContinuumBesovTightness`, `MembraneScalingLimitFour` |
| `HighFirstOrder/` | none |
| `HighTail/` | none |
| `HighSobolevLimit/` | `GaussianLipschitzConcentration`, `NormalComparison`, `IntersectionSecondMoment`, `LocalCLT`, `ContinuumBesovTightness` |
| `HighNonconvergence/` | `IntersectionSecondMoment`, `LocalCLT`, `ContinuumBesovTightness` |

Three cited results, `GreenBoundsHigh`, `HeatKernelBounds` and `VarianceScale`,
are proved unconditionally in the repository (`Sandpile/External/*Proved.lean`;
see `ASSUMPTIONS.md`) rather than assumed.  Earlier versions of `CriticalLevels/`,
`FourSobolev/`, `HighFirstOrder/`, `HighTail/`, `HighSobolevLimit/` and
`MeanGrowthLow/` carried one or more of them as hypotheses; the certified
statements now carry none of the three, and neither do the challenges above.

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
| `External.*` and their auxiliary definitions (`BallGreen.*`, `Variance.*`, `Lclt.*`, `Snell.*`, `latticeNorm`, `latticeDist`, `tailKernel`, `SameParity`, `membraneDefect`, `interCount`) | `Sandpile/External/` |

The only textual changes are the namespaces, a proof of the irreflexivity field
of `lattice` that uses no library lemma, and the `noncomputable` marker on
`planeRectangle`, which the repository gets from a `noncomputable section`.

## Solutions

Each `Solution.lean` imports the repository together with
`Audit/Support/Vocabulary.lean`, a verbatim copy of the vocabulary block that
imports only Mathlib, and proves the byte-identical statement from the
corresponding theorem of `Sandpile/MainTheorems.lean` through the bridges in
`Audit/Support/Bridge.lean` (see [`DESIGN.md`](DESIGN.md)).

`Audit/StatementRegression.lean` is a local check of the statement-identity
part of the comparator: it elaborates each statement in the challenge
environment (`Audit/Support/Statements.lean`, which imports only Mathlib and
the vocabulary), checks that each solution theorem has exactly that type and the
same universe parameters, and that it mentions no constant of the namespaces
`Sandpile` or `LatticeProb`, and prints the axioms of each solution theorem.

## Reproducing The Checks

The comparator configurations permit only

```json
["propext", "Quot.sound", "Classical.choice"]
```

and set `enable_nanoda: false`.  Each challenge elaborates standalone against
this repository's Mathlib toolchain, e.g.

```bash
bash Audit/check_standalone.sh Audit/Nontriviality/Challenge.lean
bash Audit/check_standalone.sh --vocabulary
```

with expected outcome `rc=0` and exactly one `declaration uses 'sorry'`
warning per challenge; the second command checks that the vocabulary block is
the same in every challenge and in `Audit/Support/Vocabulary.lean`.  The
solutions and the regression build with

```bash
lake build Audit.StatementRegression
```

which prints, for each of the twelve theorems, that it is identical to the
challenge statement and depends only on `propext`, `Classical.choice` and
`Quot.sound`.

**Status.**  All twelve solutions build, and the statement regression and the
axiom prints pass locally.  `leanprover/comparator` was run on all twelve
pairs on 2026-09-24, at commit `4545f0b`, and every pair passed with the Lean
kernel and with the independent nanoda kernel.  The results and the
reproduction steps are in [`COMPARATOR_RUNS.md`](COMPARATOR_RUNS.md).  The
workflow [`.github/workflows/comparator.yml`](../.github/workflows/comparator.yml)
runs the same check on request.
