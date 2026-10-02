# Comparator runs

The official `leanprover/comparator` was run on every pair in this directory on a local machine (Linux 6.17), with the Lean kernel and the independent `nanoda` kernel both enabled (every committed `comparator.json` sets `"enable_nanoda": true`).

| Tool | Revision |
|---|---|
| leanprover/comparator | `575674928e239f5bc452aab72d1dd7b0f1326494` |
| leanprover/lean4export | `v4.32.0` (`4e7915201d3f9f04470d9eae002fa695f7cdc589`) |
| Zouuup/landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` (v0.1.18) |
| ammkrn/nanoda_lib | `6ae1f0cd962f081f6c423454c5da729d841236a7` |

A pass means the comparator printed `nanoda kernel accepts the solution`, `Lean default kernel accepts the solution` and `Your solution is okay!`: the solution proves a theorem whose statement and full dependency closure match the challenge's, using only the permitted axioms.

## `BrownianScalingLimit`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (298 s) |

## `CriticalLevels`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (530 s) |

## `FourFirstOrder`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (164 s) |

## `FourGaussian`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (237 s) |

## `FourSobolev`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (391 s) |

## `HighFirstOrder`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (128 s) |

## `HighNonconvergence`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (274 s) |

## `HighSobolevLimit`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (306 s) |

## `HighTail`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (160 s) |

## `MeanGrowthFour`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (183 s) |

## `MeanGrowthLow`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (293 s) |

## `Nontriviality`

| Check | Result |
|---|---|
| Lean and nanoda kernels | passed (629 s) |

To reproduce one pair, from the repository root:

```
COMPARATOR_LANDRUN=<landrun> COMPARATOR_LEAN4EXPORT=<lean4export> COMPARATOR_NANODA=<nanoda_bin> \
  lake env <comparator>/.lake/build/bin/comparator SandpileAudit/<Pair>/comparator.json
```
