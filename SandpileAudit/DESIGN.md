# Comparator design memo: vocabulary, bridges, deltas

This memo records how the twelve comparator pairs are built, for whoever checks
or extends them.  Each pair `SandpileAudit/<Thm>/` has the same four files, and
each pair has its own bridge under `SandpileAudit/Support/`.

- `Challenge.lean` imports `Mathlib` and nothing else.  It rebuilds from Mathlib
  primitives every object its theorem mentions, states the theorem and ends in a
  single `sorry`.  This file is the object of trust: a reader checks what it
  says, not how it is proved.
- `SolutionBasic.lean` is a verbatim, mechanical copy of the vocabulary block of
  `Challenge.lean` (between `VOCABULARY-BEGIN` and `VOCABULARY-END`).  It imports
  only `Mathlib`, so the vocabulary elaborates in the solution exactly as in the
  challenge.
- `Solution.lean` imports the repository together with its own `SolutionBasic`
  and its own bridge `SandpileAudit/Support/<Thm>Bridge.lean`, restates the
  challenge theorem byte-for-byte, and proves it from the corresponding theorem
  of `Sandpile/MainTheorems.lean`.
- `comparator.json` names the challenge module, the solution module, the theorem
  and the permitted axioms (`propext`, `Classical.choice`, `Quot.sound`), and
  enables the nanoda kernel.

## 0. Solution architecture

The comparator checks that the solution theorem has the same elaborated type
as the challenge theorem, constant by constant through the whole dependency
closure.  So the vocabulary constants must elaborate in the solution exactly
as in the challenge.  The vocabulary is therefore compiled in a module that
imports **only Mathlib** (`<Thm>/SolutionBasic.lean`), and `Solution.lean` imports
the repository, that module, and the pair's bridge, and states the theorem with
the challenge's bytes.

The twelve challenges share one vocabulary block, byte-identical in each
(`bash SandpileAudit/check_standalone.sh --vocabulary` compares each challenge
with its `SolutionBasic.lean`), so the twelve `SolutionBasic.lean` files carry the
same block.  The block contains every definition that any of the twelve statements
reaches; a given challenge uses only part of it, and the rest does not enter that
theorem's dependency closure.  The block was determined mechanically: it is the
closure of the twelve certified statements under unfolding of definitions,
restricted to the namespaces `Sandpile` and `LatticeProb` (about 130
declarations).

## 1. Definitionally shared vocabulary

Every definition of the vocabulary that is neither a structure nor recursive,
and does not reach a recursive definition, is a token-for-token copy of its
source over Mathlib types, and is definitionally equal to its counterpart.
The solutions use these definitionally, with no rewriting: the `exact` that
closes each solution, and the bridges of Section 3 that are proved by the
hypothesis itself (`planarRSW`, `lssDomination`, `exteriorBoundaryConnected`,
`pittGaussianFKG`, `continuumBesovTightness`, `gaussianLipschitzConcentration`,
`normalComparison`), are checked by the kernel, which unfolds both sides.

## 2. Recursive copies and structure copies

**Recursive definitions.**  Four vocabulary definitions are recursive:
`heatKernel`, `odometer`, `killedKernel` and `membrane`.  Their copies are new
recursive definitions, compiled to their own recursors, and the elaborator
does not identify them with the originals by unfolding.  A pair's bridge proves
each one that its statement reaches equal to its counterpart as constants, by
induction on the time index (`heatKernel_eq`, `odometer_eq`, `killedKernel_eq`,
`membrane_eq`), and then proves equal to their counterparts the definitions
whose bodies reach them:
`greenTime`, `green`, `potentialKernel`, `killedGreenTime`, `killedGreen`,
`odometerLimit`, `toppledSet`, `meanOdometer`, `Continuum.diffusiveFluctuation`,
`External.tailKernel`, `External.Variance.windowKernel`,
`External.BallGreen.cutField`, `External.BallGreen.timeTail` and
`External.membraneDefect`.  Because these are equalities of constants, one
`rw` replaces every occurrence, under binders and inside types.

**Structures.**  Three vocabulary declarations are structures, hence new
inductive types: `Continuum.IsWhiteNoise`, `Continuum.IsBrownian` and
`Continuum.PlaneSymmetry`.  The bridges of the pairs that reach them convert them
field by field:

- `isBrownian_iff`: the vocabulary `IsBrownian` and the repository's are
  equivalent, in both directions, since Brownian motion occurs both as a
  hypothesis of Theorem 1.3(i)(b) and as a premise inside four cited results;
- `isWhiteNoise`: a vocabulary white noise is a repository white noise (white
  noise occurs only as a hypothesis);
- `toPlaneSymmetry`, `ofPlaneSymmetry` and `isSymmetricField_iff`: a plane
  symmetry in either form is one in the other with the same fields, and the
  symmetry predicate on planar fields, which quantifies over plane symmetries,
  transfers in both directions.

## 3. Theorem-level bridges

For each cited result that a pair's statement carries, that pair's bridge proves
that the vocabulary proposition implies the repository's: by rewriting with the equalities of Section 2
(`ballGreenBounds`, `greenBoundsHigh`, `varianceScale`, `localCLT`,
`pairedLocalCLTFour`, `heatKernelBounds`, `membraneScalingLimitFour`), by
converting the Brownian premise (`ballOccupationDensity`,
`cubeStoppingStability`, `continuumStoppingStability`,
`continuumOptimalStopping`) or the symmetry premise (`continuumRSW`), or by the
hypothesis itself.

Each pair's bridge contains exactly the declarations that its solution uses,
together with those they rest on, under the same names and in the same namespace
`SandpileAudit.Bridge` in every pair.

Each solution rewrites the vocabulary constants of its conclusion that reach a
recursive definition (`toppledSet`, `odometer`, `meanOdometer` or
`Continuum.diffusiveFluctuation`) into the repository's, and closes the goal
with `exact` of the theorem of `Sandpile/MainTheorems.lean`, applied to the
transported hypotheses.  Everything else in the statements is identified
definitionally.

## 4. Presentation deltas

None at the level of the displayed statements: each challenge theorem is the
statement of the corresponding theorem of `Sandpile/MainTheorems.lean`, which
is the frozen statement of `Sandpile/Frozen/`, with every repository and
library name replaced by its vocabulary copy.

How each statement reads the paper is recorded in
[`CORRESPONDENCE.md`](../CORRESPONDENCE.md).  The comparator does not check
that reading: it checks that the library proves exactly the displayed
statement, over definitions that can be read without the library.

## 5. What the comparator does not certify

- The cited results.  The challenges take them as hypotheses, restated in the
  vocabulary.  A proof conditional on a proposition does not show that the
  proposition is a faithful rendering of the cited theorem; that reading is
  the subject of `ASSUMPTIONS.md`.
- The faithfulness of the vocabulary to the paper.  The vocabulary is a copy
  of the definitions the repository uses, so the comparator shows that nothing
  in the statements depends on the library beyond what the vocabulary
  displays; a reader still has to check the vocabulary against the paper.

## 6. What the comparator checks

The comparator itself checks each solution statement against its challenge,
constant by constant through the whole dependency closure, the closure against
Mathlib, and the axioms of the solution against the permitted three.  Every pair
passes with the Lean kernel and with the independent nanoda kernel; see
[`COMPARATOR_RUNS.md`](COMPARATOR_RUNS.md) for the results and the reproduction
steps.

The solutions import both the repository and the vocabulary, and both declare
that the two mass laws are probability measures.  A solution statement that
picked up a repository or library constant, in particular one of the
repository's instances, would differ from its challenge in the closure check.
There is no separate local regression: the twelve solutions cannot be imported
into one module, because each pair has its own copy of the vocabulary.
