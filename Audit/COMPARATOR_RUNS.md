# Comparator runs

The official `leanprover/comparator` was run on every pair in this directory on 2026-09-24, at commit `4545f0b`, on a local machine. Each pair was checked twice: once with the Lean kernel, and once more with the independent `nanoda` kernel enabled (a temporary copy of `comparator.json` with `"enable_nanoda": true`). The committed configurations keep `enable_nanoda` false so that a reproduction needs only three tools.

| Tool | Revision |
|---|---|
| leanprover/comparator | `575674928e239f5bc452aab72d1dd7b0f1326494` |
| leanprover/lean4export | `v4.32.0` (`4e7915201d3f9f04470d9eae002fa695f7cdc589`) |
| Zouuup/landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` (v0.1.18; Linux 5.15, Landlock ABI 1 in best-effort mode) |
| ammkrn/nanoda_lib | `6ae1f0cd962f081f6c423454c5da729d841236a7` |

| Pair | Lean kernel | Lean and nanoda kernels |
|---|---|---|
| `BrownianScalingLimit` | passed (296 s) | passed (372 s) |
| `FourFirstOrder` | passed (183 s) | passed (231 s) |
| `CriticalLevels` | passed (365 s) | passed (506 s) |
| `FourGaussian` | passed (264 s) | passed (334 s) |
| `FourSobolev` | passed (259 s) | passed (335 s) |
| `HighFirstOrder` | passed (159 s) | passed (187 s) |
| `HighTail` | passed (196 s) | passed (230 s) |
| `HighNonconvergence` | passed (317 s) | passed (397 s) |
| `HighSobolevLimit` | passed (345 s) | passed (448 s) |
| `MeanGrowthFour` | passed (210 s) | passed (256 s) |
| `MeanGrowthLow` | passed (310 s) | passed (433 s) |
| `Nontriviality` | passed (397 s) | passed (498 s) |

A pass means the comparator printed `Your solution is okay!`: the solution proves a theorem whose statement and full dependency closure match the challenge's, using only the permitted axioms.

To reproduce one pair, from the repository root:

```
COMPARATOR_LANDRUN=<landrun> COMPARATOR_LEAN4EXPORT=<lean4export> \
  lake env <comparator>/.lake/build/bin/comparator Audit/<Pair>/comparator.json
```

## Run of 2026-09-28

Every pair was run again on 2026-09-28, at commit `8207a73`, against the current
statements and the published Lattice-Probability pin, on a second local machine
(Linux 6.17), with the same tool revisions as above.

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
