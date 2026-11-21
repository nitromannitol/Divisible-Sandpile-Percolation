# Comparator runs

The official `leanprover/comparator` was run on all seventeen pairs in this directory on a local machine (Linux 6.17), with the Lean kernel and the independent `nanoda` kernel both enabled (every committed `comparator.json` sets `"enable_nanoda": true`).  All seventeen pairs were run against the repository at commit `0f0f9369d247243a9d107b5725a5bcdc73858456`.  The dependencies are those pinned in `lake-manifest.json` (mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`, Lattice-Probability `751040ea092fcf9ae7de4edb7e4f89af4c5291ec`) under `leanprover/lean4:v4.35.0-rc2`.

| Tool | Revision |
|---|---|
| leanprover/comparator | `575674928e239f5bc452aab72d1dd7b0f1326494` |
| leanprover/lean4export | `v4.35.0-rc2` (`6cea97789dc088ea47fcea15692db85685aedac5`) |
| Zouuup/landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` (v0.1.18) |
| ammkrn/nanoda_lib | `6ae1f0cd962f081f6c423454c5da729d841236a7` |

A pass means the comparator printed `nanoda kernel accepts the solution`, `Lean default kernel accepts the solution` and `Your solution is okay!`: the solution proves a theorem whose statement and full dependency closure match the challenge's, using only the permitted axioms.  The host kernel supports an older Landlock interface than the one `landrun` requests, so `landrun` ran in its best-effort mode and its filesystem restriction was not enforced in these runs; the statement, closure, axiom and kernel checks do not depend on it.  The times are wall-clock times, including the builds of the challenge and solution modules.

## `BrownianScalingLimit`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (435 s) |

## `BrownianScalingLimitUnconditional`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (477 s) |

## `CriticalLevels`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (625 s) |

## `CriticalLevelsUnconditional`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (730 s) |

## `FourFirstOrder`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (265 s) |

## `FourGaussian`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (399 s) |

## `FourSobolev`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (457 s) |

## `FourSobolevUnconditional`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (516 s) |

## `HighFirstOrder`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (242 s) |

## `HighNonconvergence`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (479 s) |

## `HighSobolevLimit`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (660 s) |

## `HighTail`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (217 s) |

## `MeanGrowthFour`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (256 s) |

## `MeanGrowthLow`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (389 s) |

## `MeanGrowthLowUnconditional`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (419 s) |

## `Nontriviality`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (609 s) |

## `NontrivialityUnconditional`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (668 s) |

To reproduce one pair, from the repository root:

```
COMPARATOR_LANDRUN=<landrun> COMPARATOR_LEAN4EXPORT=<lean4export> COMPARATOR_NANODA=<nanoda_bin> \
  lake env <comparator>/.lake/build/bin/comparator SandpileAudit/<Pair>/comparator.json
```
