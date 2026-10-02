# Comparator runs

The official `leanprover/comparator` was run on every pair in this directory, against the statements of this repository, on a local machine (Linux 6.17). Each pair was checked twice: once with the Lean kernel, and once more with the independent `nanoda` kernel enabled (a temporary copy of `comparator.json` with `"enable_nanoda": true`). The committed configurations keep `enable_nanoda` false so that a reproduction needs only three tools.

| Tool | Revision |
|---|---|
| leanprover/comparator | `575674928e239f5bc452aab72d1dd7b0f1326494` |
| leanprover/lean4export | `v4.32.0` (`4e7915201d3f9f04470d9eae002fa695f7cdc589`) |
| Zouuup/landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` (v0.1.18) |
| ammkrn/nanoda_lib | `6ae1f0cd962f081f6c423454c5da729d841236a7` |

| Pair | Lean kernel | Lean and nanoda kernels |
|---|---|---|
| `BrownianScalingLimit` | passed (187 s) | passed (252 s) |
| `CriticalLevels` | passed (238 s) | passed (335 s) |
| `FourFirstOrder` | passed (113 s) | passed (146 s) |
| `FourGaussian` | passed (156 s) | passed (208 s) |
| `FourSobolev` | passed (159 s) | passed (212 s) |
| `HighFirstOrder` | passed (95 s) | passed (118 s) |
| `HighNonconvergence` | passed (185 s) | passed (251 s) |
| `HighSobolevLimit` | passed (208 s) | passed (282 s) |
| `HighTail` | passed (113 s) | passed (146 s) |
| `MeanGrowthFour` | passed (113 s) | passed (146 s) |
| `MeanGrowthLow` | passed (189 s) | passed (258 s) |
| `Nontriviality` | passed (238 s) | passed (339 s) |

A pass means the comparator printed `Your solution is okay!`: the solution proves a theorem whose statement and full dependency closure match the challenge's, using only the permitted axioms.

To reproduce one pair, from the repository root:

```
COMPARATOR_LANDRUN=<landrun> COMPARATOR_LEAN4EXPORT=<lean4export> \
  lake env <comparator>/.lake/build/bin/comparator Audit/<Pair>/comparator.json
```
