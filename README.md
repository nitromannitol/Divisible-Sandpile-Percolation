# Quantitative explosion and percolation of the divisible sandpile

A machine-checked **Lean 4** formalization of the paper

> Ahmed Bou-Rabee and Christoforos Panagiotis,
> *Quantitative explosion and percolation of the divisible sandpile*,
> [arXiv:2609.02829](https://arxiv.org/abs/2609.02829).

The paper's source, bibliography and figures are included under [`paper/`](paper/). The
paper's three main theorems (Theorems 1.1 and 1.2 and the ten parts of Theorem 1.3, 12 Lean
theorems in all) are proved, in the form in which its introduction states them, from results
cited from the literature that enter as explicit hypotheses of the theorems that use them:
10 of the 13 cited results are hypotheses of these theorems, and 5 of the 12 take none. See
[Assumed literature inputs](#assumed-literature-inputs). Every other labelled theorem, lemma,
proposition and corollary of the paper is formalized as well.

The development is built on [mathlib](https://github.com/leanprover-community/mathlib4) and on
the shared library [Lattice-Probability](https://github.com/nitromannitol/Lattice-Probability)
(`LatticeProb`), a library of lattice probability and potential theory.

[![CI](https://github.com/nitromannitol/Divisible-Sandpile-Percolation/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/nitromannitol/Divisible-Sandpile-Percolation/actions/workflows/build.yml)
[![Comparator audit](https://github.com/nitromannitol/Divisible-Sandpile-Percolation/actions/workflows/comparator.yml/badge.svg?branch=main)](https://github.com/nitromannitol/Divisible-Sandpile-Percolation/actions/workflows/comparator.yml)

## What is proved

The divisible sandpile on `ℤ^d` starts from an i.i.d. mass `σ(x)` at each site. A site is
unstable when its mass exceeds one; an unstable site topples, keeping one unit and sharing the
excess equally among its `2d` neighbours, and at each discrete step every unstable site
topples at once. Writing `u_t(x)` for the mass `x` has sent to each neighbour in the first `t`
steps, `u_0 ≡ 0` and

    u_{t+1}(x) = ( (σ(x) − 1)/(2d) + (1/(2d)) Σ_{y∼x} u_t(y) )_+ .

At mean `ρ = E σ(0)` the sandpile either stabilizes at every site or explodes at every site;
it stabilizes for `ρ < 1` and explodes for `ρ = 1` with positive finite variance. The paper
asks how fast it explodes at `ρ = 1`, and what the toppled set
`𝒯^{(ρ)} = {x : u_∞^{(ρ)}(x) > 0}` looks like for `ρ < 1`.

Theorem 1.1 says that for every `d ≥ 2`, under a uniform variance lower bound and a uniform
exponential moment along a family of laws, there is `ρ₊ < 1` such that `𝒯^{(ρ)}` contains an
infinite nearest-neighbour component almost surely for every `ρ ∈ (ρ₊, 1)`: the toppled set
percolates below mean one. It follows from Theorem 1.2, which gives an explicit percolating
level set of the finite-time odometer at mean one: for every `t` large,
`{x : u_t(x) > c h(t)}` contains an infinite component almost surely, with
`h(t) = t^{(4−d)/4}` for `d ∈ {2,3}`, `log t` for `d = 4` and `(log t)^{2/d}` for `d ≥ 5`.
Theorem 1.3 collects the growth and scaling results at mean one: the growth of `E u_t(0)` and
the parabolic scaling limit to a Brownian optimal-stopping value in `d ≤ 3`; the logarithmic
growth, the first-order determinism, the Gaussian fluctuations with variance
`4 Var(ζ(0))/π²` and the superdiffusive limit to the membrane model in `d = 4`; and in
`d ≥ 5` the first-order determinism, the tail-determined order
`(log t)^{1/min{γ,d/2}}` of the mean, the weighted membrane limits, and a scenery whose
rescaled fluctuations have uncountably many distinct subsequential limits. The model is
stated precisely in [Standing assumptions and scope](#standing-assumptions-and-scope).

The 12 main results, formalized as stated in the introduction of the paper, are collected in
[`Sandpile/MainTheorems.lean`](Sandpile/MainTheorems.lean). Each is proved by `exact` of its
certified counterpart in `Sandpile/Frozen/`, so the statements displayed there are the
certified ones. The hypotheses listed are the cited results each theorem carries; see
[Assumed literature inputs](#assumed-literature-inputs).

| Paper | Lean declaration | Content |
| --- | --- | --- |
| Theorem 1.1 (label `thm:main-nontriviality`) | `Sandpile.percolation_below_criticality` | the toppled set percolates for means close to one |
| Theorem 1.2 (label `thm:main-critical-level-percolation`) | `Sandpile.critical_level_percolation` | an explicit level set of the finite-time odometer percolates at mean one |
| Theorem 1.3(i)(a) | `Sandpile.mean_growth_le_three` | growth of `E u_t(0)` for `d ≤ 3` |
| Theorem 1.3(i)(b) | `Sandpile.brownian_scaling_limit` | Brownian optimal-stopping scaling limit for `d ≤ 3` |
| Theorem 1.3(ii)(a), first clause | `Sandpile.mean_growth_four` | logarithmic growth of `E u_t(0)` for `d = 4` |
| Theorem 1.3(ii)(a), second clause | `Sandpile.four_first_order` | first-order determinism for `d = 4` |
| Theorem 1.3(ii)(b) | `Sandpile.four_gaussian` | Gaussian fluctuations for `d = 4` |
| Theorem 1.3(ii)(c) | `Sandpile.four_sobolev` | membrane-model limit for `d = 4` |
| Theorem 1.3(iii)(a) | `Sandpile.high_first_order` | first-order determinism for `d ≥ 5` |
| Theorem 1.3(iii)(b) | `Sandpile.high_tail` | tail-determined order of the mean for `d ≥ 5` |
| Theorem 1.3(iii)(c) | `Sandpile.high_sobolev_limit` | weighted membrane limits for `d ≥ 5` |
| Theorem 1.3(iii)(d) | `Sandpile.high_nonconvergence` | a scenery with uncountably many subsequential limits, `d ≥ 5` |

**Theorem 1.1 (percolation below criticality, `thm:main-nontriviality`).** For `d ≥ 2` and a
family of laws `μ_ρ` of mean `ρ`, with `Var_{μ_ρ} σ(0) ≥ ν₀²` and
`E_{μ_ρ} e^{θ₀|σ(0)−ρ|} ≤ K₀` for `ρ ∈ [ρ₀, 1)`, there is `ρ₊ ∈ [ρ₀, 1)` such that for every
`ρ ∈ (ρ₊, 1)` the toppled set contains an infinite component almost surely. Hypotheses:
`PlanarRSW`, `LSSDomination`, `ExteriorBoundaryConnected`, `ContinuumRSW`,
`BallOccupationDensity`, `CubeStoppingStability`.

**Theorem 1.2 (critical level percolation, `thm:main-critical-level-percolation`).** There are
`c > 0` and `t₀`, depending only on `d, ν₀, θ₀, K₀`, such that for every mean-one law with
those bounds and every `t ≥ t₀`, `{x : u_t(x) > c h(t)}` contains an infinite component almost
surely. Hypotheses: the same seven as Theorem 1.1.

**Theorem 1.3(i) (`d ≤ 3`).**

1. *(a) Mean growth.* `t^{−(4−d)/4} E u_t(0)` converges to a positive limit. Hypotheses:
   `ContinuumStoppingStability`, `ContinuumOptimalStopping`.
2. *(b) Scaling limit.* The multilinear interpolation of `R^{−(2−d/2)} u_{⌊TR²⌋}` converges in
   finite-dimensional distributions to the Brownian stopping value `𝒰(T, ·)` and is tight in
   the uniform norm on compact sets. Hypothesis: `ContinuumStoppingStability`.

**Theorem 1.3(ii) (`d = 4`).**

1. *(a) Growth and first order.* `c log t ≤ E u_t(0) ≤ C log t` for `t ≥ 2`, and
   `u_t(x)/E u_t(0) → 1` in `L²` and almost surely. No hypotheses.
2. *(b) Gaussian fluctuations.* `(u_t(0) − E u_t(0))/√(log t)` converges in distribution to
   `N(0, 4 Var(ζ(0))/π²)`, and `Var(u_t(0))/log t` converges to the same constant. No
   hypotheses.
3. *(c) Membrane model.* The centred fields at diffusive times are tight in `H^{−s}_loc`, and
   at the superdiffusive times `⌊R^α⌋`, `α > 2`, they converge modulo constants to the
   membrane model `𝒢_4`. Hypotheses: `ContinuumBesovTightness`, `MembraneScalingLimitFour`.

**Theorem 1.3(iii) (`d ≥ 5`).**

1. *(a) First order.* `u_t(x)/E u_t(0) → 1` in `L²` and almost surely, and
   `E u_t(0) ≥ c (log t)^{2/d}` for all large `t`. No hypotheses.
2. *(b) Tail-determined order.* If `−log P(ζ(0) ≤ −s) ≍ s^γ` with `γ ≥ 1`, `γ ≠ d/2`, then
   `E u_t(0) ≍ (log t)^{1/min{γ,d/2}}`. No hypotheses.
3. *(c) Weighted membrane limits.* The fields
   `R^{(d−4)/2}(u_{⌊TR²⌋} − E u_{⌊TR²⌋}(0))^{(R)}` converge in `H^{−s}_loc`, `s > (d−4)/2`, to
   `ℋ_{1,T}` for Gaussian scenery and to `ℋ_{1−1/α,T}` for atomless scenery bounded above with
   a regularly varying lower tail of index `α > 2`. Hypothesis:
   `ContinuumBesovTightness`.
4. *(d) Non-convergence.* There is a law with mean zero, variance one, a smooth positive
   density and an exponential moment whose rescaled fluctuations are tight in `H^{−s}_loc` but
   have uncountably many distinct subsequential limits, and so do not converge. Hypothesis:
   `ContinuumBesovTightness`.

In Lean, the fields are fixed by their one-site law through `centeredMassLaw d ν` or
`massLaw d μ`; Theorem 1.3 is registered one part per node (ten nodes). Two further nodes
prove that white noise and Brownian motion exist (`Sandpile/Continuum/`), so that the
predicates over which the statements quantify are not vacuous.

This repository formalizes every labelled theorem, lemma, proposition and corollary of the
paper: 58 labelled statements, registered as 69 nodes in `Sandpile/Frozen/` because a
statement in several parts is registered one part per node.

## Corrections to the published version

The formalization follows `paper/sandpile.tex`, a corrected text of the paper: it is
[arXiv:2609.02829v1](https://arxiv.org/abs/2609.02829v1) with nine corrections.
[`paper/CHANGES_FROM_ARXIV.md`](paper/CHANGES_FROM_ARXIV.md) lists every change against the
arXiv version.

## Standing assumptions and scope

1. **Every theorem is about every law that satisfies its hypotheses.** The statements are for
   the divisible sandpile on `ℤ^d` with i.i.d. masses, in the dimensions stated in each
   theorem (`d ≥ 2` in Theorem 1.1, and `d ≤ 3`, `d = 4` and `d ≥ 5` in the three parts of
   Theorem 1.3), for every one-site law, or family of laws, that satisfies the moment,
   variance and tail hypotheses spelled out in the Lean statement. The fields are fixed by
   their one-site law, through `centeredMassLaw d ν` or `massLaw d μ`; an i.i.d. field is
   determined by its one-site law. In Theorem 1.1 the threshold `ρ₊` is bound after the
   witnesses `ρ₀, ν₀, θ₀, K₀` and before `ρ`, the reading under which the paper's membership
   `ρ₊ ∈ [ρ₀, 1)` holds.
2. **Axioms and incomplete proofs.** The library contains no `sorry`, no `admit`, no
   `native_decide` and no new `axiom`. The axiom report of each main theorem consists of
   exactly `propext`, `Classical.choice` and `Quot.sound`. The main theorems take 11 cited
   results as explicit hypotheses, listed under
   [Assumed literature inputs](#assumed-literature-inputs); nothing else is assumed.
3. **What is not formalized.** The proof-overview, related-work and open-problem subsections,
   the unlabelled remarks (including the nonpercolation remark at low mean, which quotes a
   Peierls argument of Fey, Meester and Redig rather than proving one), the labelled remark
   `rem:kernel-concentration`, and the figures.
4. **Conventions that matter for reading the statements.**
   - Mathlib has no Sobolev space, so every convergence in `H^{−s}_loc` is stated as
     convergence in distribution of each pairing to the matching centred Gaussian together
     with tightness of the `H^{−s}(D)` norms, and convergence in `C_loc` likewise with the
     uniform norm on compact sets.
   - Mathlib constructs neither white noise nor Brownian motion, so both are predicates and
     each statement is quantified over a probability space carrying them;
     `Sandpile.Continuum.exists_isWhiteNoise` and `Sandpile.Continuum.exists_isBrownian` show
     that neither predicate is vacuous.
   - An exponential-moment bound `E e^{θ₀|σ(0)−ρ|} ≤ K₀` is stated together with the
     integrability of the exponential, since the Bochner integral of a non-integrable
     function is zero.
   - The infinite Green field is the limit of the finite-box partial sums rather than an
     unordered `tsum`; the crossing statements carry the paper's continuous-modification
     clause as an explicit almost-sure hypothesis, and the continuum crossing comparison is
     stated for a field on a probability space; and the continuum value is read off a
     modification of the Gaussian heat potential that is continuous and of polynomial growth
     on each finite strip.
5. **Explicit versus implicit.** The correspondence file records the three standing
   conventions the Lean headers refer to by name, the cited inputs of each node, and every
   place where the form of a Lean statement differs from the paper's.
6. **Statements without a formal counterpart.** Every labelled statement of the paper is
   registered: one Lean declaration per theorem, lemma, proposition and corollary, or per part
   of one, and one proposition per cited result. The paper-to-Lean map, node by node, is
   [`CORRESPONDENCE.md`](CORRESPONDENCE.md), with a generated table of every registered
   statement with its Lean name and paper location.

## Assumed literature inputs

Results that the paper quotes from the literature are stated in Lean as propositions in
`Sandpile/External/`. There are 13 such propositions that this repository does not prove, and
every theorem whose proof uses one takes it as an explicit hypothesis, so the statement shows
exactly which of them it rests on. [`ASSUMPTIONS.md`](ASSUMPTIONS.md) lists all 13 with their
verbatim Lean statements. Ten are hypotheses of the main theorems:

| Hypothesis | Content | Source | Used by |
| --- | --- | --- | --- |
| `Sandpile.External.PlanarRSW` (`hRSW`) | Russo–Seymour–Welsh crossing comparison for symmetric positively associated planar site fields | Köhler-Schindler and Tassion, Theorem 1 and Comment 1 | Theorems 1.1, 1.2 |
| `Sandpile.External.ContinuumRSW` (`hRSWc`) | the same crossing comparison for symmetric positively associated continuous planar fields (superlevel sets) | Köhler-Schindler and Tassion, Theorem 1 and Comment 1 | Theorems 1.1, 1.2 |
| `Sandpile.External.LSSDomination` (`hLSS`) | a planar stationary `k`-dependent site process with one-site density at least `1 − δ` has an infinite component almost surely | Liggett, Schonmann and Stacey (1997), Corollary 1.4 | Theorems 1.1, 1.2 |
| `Sandpile.External.ExteriorBoundaryConnected` (`hBoundary`) | the exterior vertex boundary of a finite `*`-connected subset of `ℤ^d` is `*`-connected | Timár, Theorem 3 | Theorems 1.1, 1.2 |
| `Sandpile.External.BallOccupationDensity` (`hOcc`) | Green function, or expected occupation density, of Brownian motion killed on exiting a Euclidean ball | Mörters and Peres, *Brownian Motion*, Chapter 3 | Theorems 1.1, 1.2 |
| `Sandpile.External.CubeStoppingStability` (`hCube`) | cube-killed version of the stability of optimal-stopping values, with the killed invariance principle | Coquet and Toldo (2007), Theorem 3 and Corollary 4 | Theorems 1.1, 1.2 |
| `Sandpile.External.ContinuumStoppingStability` (`hStab`) | stability of optimal-stopping values under uniform convergence of the reward, and an invariance principle for the stopped walk | Coquet and Toldo (2007), Theorem 3 and Corollary 4 | Theorems 1.3(i)(a), 1.3(i)(b) |
| `Sandpile.External.ContinuumOptimalStopping` (`hOS`) | finite-horizon optimal stopping for Brownian motion with a continuous gain of polynomial growth | Peskir and Shiryaev, Theorem 2.2 | Theorem 1.3(i)(a) |
| `Sandpile.External.ContinuumBesovTightness` (`hBesov`) | tightness criterion in `H^{−s}_loc` for a jointly measurable field, from covariance bounds | Furlan and Mourrat, Theorem 2.30 (`p = q = 2`) | Theorems 1.3(ii)(c), 1.3(iii)(c), 1.3(iii)(d) |
| `Sandpile.External.MembraneScalingLimitFour` (`hMembrane`) | scaling limit of the four-dimensional discrete membrane field | Cipriani, Hazra and Ruszel, Theorem 2; Cipriani, Dan and Hazra, Theorem 3.11 | Theorem 1.3(ii)(c) |

The other three, `MultivariateBerryEsseen`, `RellichKondrachovNegSobolev` and
`BrownianExitStep`, are hypotheses of intermediate statements in `Sandpile/Frozen/` only.
Theorems 1.3(ii)(a) (both clauses), 1.3(ii)(b), 1.3(iii)(a) and 1.3(iii)(b) take no
hypothesis.

Thirteen further results the paper cites without proof are **proved unconditionally in this
repository** (`Sandpile/External/*Proved.lean`) and so are not carried as a hypothesis by any
main theorem: the `d ≥ 5` Green-function estimates, the finite-time variance scale, the
heat-kernel bounds, the discrete optimal-stopping representation of the odometer, the
determination of a centred Gaussian law by its covariance, Pinsker's inequality, the second
intersection moment of two independent walks, the local central limit theorem, its paired
dimension-four form, the ball-killed Green bounds, Pitt's Gaussian FKG theorem (Pitt 1982),
Gaussian concentration for Lipschitz functionals (Borell; Tsirelson, Ibragimov and Sudakov), and
the normal comparison inequality (Li and Shao, Corollary 2.1). The certified statements of
Theorems 1.1 and 1.2 in `Sandpile/Frozen/` still carry Pitt's theorem, and that of
Theorem 1.3(iii)(c) Gaussian concentration and the normal comparison inequality, as hypotheses;
`Sandpile/MainTheorems.lean` discharges them.

## Registered statements

Every labelled statement of the paper is registered in
[`ledger/manifest.yaml`](ledger/manifest.yaml). A registered statement's text between the lines
`-- FROZEN-STATEMENT-BEGIN` and `-- FROZEN-STATEMENT-END` is pinned by the SHA-256 of those
bytes in the manifest, together with the line range in `paper/sandpile.tex` and the `\label`
it transcribes; the proof after the end marker may be rewritten freely. In the manifest, a
registered statement is `PROVED` when it is proved with an axiom closure of exactly the three
standard axioms and has passed an independent refutation-first audit, `SEALED` when it is
proved but not yet audit-promoted, and `FROZEN` when it is a cited result assumed rather than
proved. Every registered statement is pinned by hash; only the `FROZEN` ones are assumed.

<!-- STATUS-BEGIN (generated by tools/sync_docs.py) -->

Status: **99 registered statements: 86 `PROVED/SEALED`, proved here, and 13 `FROZEN`, cited results that are assumed.**  The 86 `PROVED/SEALED` nodes are machine-checked and no proved
node's axiom closure contains `sorryAx`.  The 13 `FROZEN` nodes are cited results, stated in
`Sandpile/External/` and carried as explicit hypotheses by the theorems
that use them; they are assumed here, not proved.  Run
`python3 tools/check_axioms.py` to confirm.  Counts here are generated
from `ledger/manifest.yaml` by `python3 tools/sync_docs.py`; do not
edit them by hand and do not trust a count in prose that the checkers
have not confirmed.

<!-- STATUS-END -->

These words are used throughout with fixed meanings.

| term | meaning |
|---|---|
| **registered statement**, also called a **node** | one Lean declaration transcribing one statement of the paper, or one result the paper cites. Each has an entry in `ledger/manifest.yaml`. |
| **frozen statement** | the declaration's text between the lines `-- FROZEN-STATEMENT-BEGIN` and `-- FROZEN-STATEMENT-END`, pinned by the SHA-256 of those bytes. It cannot change without the change being recorded in the manifest. The proof after the end marker may be rewritten freely. |
| **`PROVED`** | the node is **proved and independently audited** here: a complete proof, whose axiom closure contains only `propext`, `Classical.choice` and `Quot.sound`, and no defect was found by a refutation-first audit. |
| **`SEALED`** | the node is **proved** here but not yet promoted to `PROVED`: a complete proof with the same three-axiom closure, awaiting independent audit. |
| **`FROZEN`** | the node is **assumed**, not proved: a result the paper quotes from the literature, stated as a proposition in `Sandpile/External/` and carried as an explicit hypothesis by every theorem whose proof uses it. Every one is listed with its statement in [`ASSUMPTIONS.md`](ASSUMPTIONS.md). |
| **`DRAFT_SORRY`** | the statement is pinned but its proof is still open, registered as a `sorry`. |
| **cited input**, **external** | a `FROZEN` node, in the sense above. |
| **axiom closure** | the axioms a proof ultimately rests on, as reported by Lean's `#print axioms`. |
| **`sorryAx`** | the axiom Lean inserts for an unproved `sorry`; its presence in an axiom closure means the result is not proved. |

The word *frozen* carries two senses, so it is worth separating them: every registered
statement is frozen in the sense of being **pinned by hash**, while the state `FROZEN` marks
the subset that is **assumed rather than proved**.

Two checkers compare each Lean statement with the paper rather than with a hash.
`tools/check_clauses.py` counts the assertions of the paper statement and the top-level
conjuncts of the Lean conclusion, and requires a written reading of every node saying what
each side asserts. `tools/check_exponents.py` extracts the exponents from both sides and
matches them, following the definitions a Lean statement names; anything the paper has and
Lean does not must be explained per node or the check fails. In each frozen statement whose
conclusion has a real existential constant, `tools/check_constants.py` checks that no paper
parameter is bound before it. The certificate of the build and of each node's axiom closure is
[`CERTIFICATE.md`](CERTIFICATE.md).

## Guarantees

- **No `sorry`.** The library has none, and `tools/check_manifest.py` rejects any `sorry`
  outside a registered `DRAFT_SORRY` node, of which there is none. The 12 comparator
  challenges under [`SandpileAudit/`](SandpileAudit/) each contain one intentional
  statement-level `sorry`, which the corresponding solution file proves.
- **Standard axioms only.** The axiom report of each of the 12 main theorems lists exactly
  `propext`, `Classical.choice` and `Quot.sound`.
  [`Sandpile/Meta/AxiomsAudit.lean`](Sandpile/Meta/AxiomsAudit.lean) prints the reports, the
  `Axiom audit` step of the CI workflow [`build.yml`](.github/workflows/build.yml) builds that
  module and fails on any warning or `sorry`, and `python3 tools/check_axioms.py` checks the
  axiom closure of every registered statement. The cited results are hypotheses, not axioms.
- **Builds from a clean checkout.** In continuous integration, `lake build` of a fresh
  checkout completes 10,229 jobs without error, and the build fails on any warning or `sorry`
  warning.
- **Pinned statements.** Every registered statement is pinned by the SHA-256 of its text in
  [`ledger/manifest.yaml`](ledger/manifest.yaml), checked by
  `python3 tools/check_manifest.py`.
- **Independent check of the statements.** The 12 main theorems are restated in
  [`SandpileAudit/`](SandpileAudit/) using mathlib alone, with every definition rebuilt from
  mathlib primitives (no project or library definitions), one challenge file per theorem:
  [`Nontriviality`](SandpileAudit/Nontriviality/Challenge.lean),
  [`CriticalLevels`](SandpileAudit/CriticalLevels/Challenge.lean),
  [`MeanGrowthLow`](SandpileAudit/MeanGrowthLow/Challenge.lean),
  [`BrownianScalingLimit`](SandpileAudit/BrownianScalingLimit/Challenge.lean),
  [`MeanGrowthFour`](SandpileAudit/MeanGrowthFour/Challenge.lean),
  [`FourFirstOrder`](SandpileAudit/FourFirstOrder/Challenge.lean),
  [`FourGaussian`](SandpileAudit/FourGaussian/Challenge.lean),
  [`FourSobolev`](SandpileAudit/FourSobolev/Challenge.lean),
  [`HighFirstOrder`](SandpileAudit/HighFirstOrder/Challenge.lean),
  [`HighTail`](SandpileAudit/HighTail/Challenge.lean),
  [`HighSobolevLimit`](SandpileAudit/HighSobolevLimit/Challenge.lean) and
  [`HighNonconvergence`](SandpileAudit/HighNonconvergence/Challenge.lean). Each challenge
  rebuilds every definition the statement reaches: the lattice, i.i.d. laws, the heat kernel
  and the Brownian exit time as in Lattice-Probability; the odometer, the walk and its
  stopping problems; the continuum kernels, Sobolev norms, white noise, Brownian motion and the
  Brownian stopping values; the planar crossing events and continuum planar fields; and the
  cited results it assumes. The solution file proves the statement from the library through the
  pair's bridge in `SandpileAudit/Support/`, and
  [leanprover/comparator](https://github.com/leanprover/comparator) checks that the statement
  is proved, with only the three standard axioms, through independent implementations of the
  Lean kernel. See [`SandpileAudit/README.md`](SandpileAudit/README.md) and
  [`SandpileAudit/COMPARATOR_RUNS.md`](SandpileAudit/COMPARATOR_RUNS.md).
- **Pinned toolchain and dependencies.** Lean `v4.32.0`; mathlib at revision
  `81a5d257c8e410db227a6665ed08f64fea08e997` and Lattice-Probability at commit
  `9d44b4d4670df393bb86ac5a4e042f215001cddf`, recorded in [`lean-toolchain`](lean-toolchain),
  [`lakefile.lean`](lakefile.lean) and [`lake-manifest.json`](lake-manifest.json) (see
  [Building](#building)).
- **The paper is part of the repository.** The statement map refers to the version in
  [`paper/`](paper/), pinned to the SHA-256
  `886793b75289a92d7acbbf93231f5b86a6b1eae1e444e64751a08193e707d5ca` of
  `paper/sandpile.tex`.

## Size

The library contains 1,141 Lean files with 198,128 physical lines, on top of mathlib and
Lattice-Probability. The count covers `Sandpile.lean` and `Sandpile/`. The comparator sources
(48 files, 29,413 lines) are counted separately.

## Building

Install [elan](https://github.com/leanprover/elan). The toolchain is pinned in
[`lean-toolchain`](lean-toolchain), and Lake fetches the dependencies.

```bash
lake exe cache get   # prebuilt mathlib
lake build
```

Lattice-Probability has no prebuilt cache, so the first build compiles it as well as the
library. `import Sandpile` loads the main theorems and what they use, and
`import Sandpile.MainTheorems` loads the main theorems and what they use.

The dependencies are public repositories, pinned to exact commits in
[`lake-manifest.json`](lake-manifest.json):

- mathlib: `https://github.com/leanprover-community/mathlib4` at
  `81a5d257c8e410db227a6665ed08f64fea08e997`.
- Lattice-Probability: `https://github.com/nitromannitol/Lattice-Probability` at
  `9d44b4d4670df393bb86ac5a4e042f215001cddf`.

To reproduce the axiom reports and build the comparator libraries:

```bash
lake build Sandpile.Meta.AxiomsAudit   # print the axioms of the twelve main theorems
lake build SandpileAudit               # the comparator challenges and solutions
```

The checkers in `tools/` need Python 3 and PyYAML (`pip install pyyaml`). `check_axioms.py` and
`check_warnings.py` run Lean; the others read the manifest, the paper and the Lean sources.

| command | what it guarantees |
|---|---|
| `python3 tools/check_manifest.py` | every node's file holds exactly one frozen block whose SHA-256 equals `frozen_sha256` and which declares exactly the node's `export`; every file in `Sandpile/Frozen/` belongs to one node; `Sandpile/` and `Sandpile.lean` contain no `axiom`, `admit` or `sorryAx`, and `sorry` occurs only in files of `DRAFT_SORRY` nodes (none is registered) |
| `python3 tools/check_axioms.py` | runs `#print axioms` on every manifest export; each closure is its registered one, and none contains `sorryAx` |
| `python3 tools/check_warnings.py` | runs `lake build Sandpile` and fails if it emits any Lean warning other than one `declaration uses 'sorry'` per `DRAFT_SORRY` node |
| `python3 tools/check_constants.py` | in a frozen statement whose conclusion has a real existential constant, no paper parameter is bound before it |
| `python3 tools/check_coverage.py` | every labelled theorem, lemma, proposition and corollary of `paper/sandpile.tex` is named in the `source` of some manifest node |
| `python3 tools/check_clauses.py` | compares the assertion count of each paper statement with the conjunct count of its Lean statement, and requires a recorded reading of every node |
| `python3 tools/check_exponents.py` | compares the exponents written in a paper statement with those in its Lean statement and the definitions it names |

Also in `tools/`: `paper_anchors.py` and `paper_citations.py` check the
`sandpile.tex:<lines>` ranges in the manifest and in the Lean docstrings against the paper's
labels; `sync_docs.py` checks (`--write` regenerates) the status block of this file and the
registered-statements table of `CORRESPONDENCE.md`; `assumptions.py` regenerates
`ASSUMPTIONS.md` (`--check` verifies it is current); `certificate.py` regenerates
`CERTIFICATE.md`; `freeze.py` registers or refreshes a node in the manifest. See
[`CONTRIBUTING.md`](CONTRIBUTING.md) for further building notes.

## Running the comparators

Each comparator pair has a configuration `SandpileAudit/<Pair>/comparator.json`, for `<Pair>`
one of `Nontriviality`, `CriticalLevels`, `MeanGrowthLow`, `BrownianScalingLimit`,
`MeanGrowthFour`, `FourFirstOrder`, `FourGaussian`, `FourSobolev`, `HighFirstOrder`,
`HighTail`, `HighSobolevLimit` and `HighNonconvergence`, that permits exactly `propext`,
`Classical.choice` and `Quot.sound` and enables the independent nanoda kernel. The comparator
checks that the solution proves the challenge statement, compares their dependency closures,
and replays the proof with the Lean and NanoDa kernels.

To run one pair locally, build `leanprover/comparator`, `lean4export`, `landrun` and
`nanoda_lib` at the revisions pinned in
[`.github/workflows/comparator.yml`](.github/workflows/comparator.yml) (also recorded in
[`SandpileAudit/COMPARATOR_RUNS.md`](SandpileAudit/COMPARATOR_RUNS.md)), and from the
repository root run:

```bash
COMPARATOR_LANDRUN=<landrun> COMPARATOR_LEAN4EXPORT=<lean4export> COMPARATOR_NANODA=<nanoda_bin> \
  lake env <comparator>/.lake/build/bin/comparator SandpileAudit/<Pair>/comparator.json
```

A pair passes when the comparator prints `Your solution is okay!`. The comparator workflow
runs the twelve pairs one after the other in a single job on GitHub-hosted runners.

There are two continuous-integration workflows: **CI** builds the library, builds the axiom
audit and checks the frozen statements; **Comparator audit** checks all 12 challenge/solution
pairs. Both run on pushes to `main` that change Lean files, `tools/`, `paper/`, `ledger/`,
`formalization.yaml` or the build configuration, and can be started manually from the
[Actions page](https://github.com/nitromannitol/Divisible-Sandpile-Percolation/actions). See
[`CONTRIBUTING.md`](CONTRIBUTING.md) for build conventions.

## Repository layout

```text
Sandpile.lean             the root module, importing the main theorems and what they use
Sandpile/
  MainTheorems.lean       the main theorems, stated in full
  Frozen/                 the certified statement surface, one frozen statement per file
  External/               the cited results, each a frozen Prop; the *Proved.lean files prove
                          ten of them
  Support/                the paper-specific definitions and lemmas the frozen statements are
                          proved from; general probability and analysis (Efron–Stein, smooth
                          maxima, weighted CLT, Taylor comparison, Laplace and
                          exponential-moment bounds, Gaussian tails, Sobolev norms) are
                          imported from Lattice-Probability
  Continuum/              white noise, Brownian motion, the continuum fields and stopping values
  Meta/AxiomsAudit.lean   the axiom report, compiled by `lake build`, not imported by the root
  Basic.lean              the odometer, its limit, the toppled set, the mass law
  Law.lean                the centred mass law and the mean odometer
  Walk.lean               the heat and Green kernels, the walk and its stopping problems
SandpileAudit/            the mathlib-only restatements and their solutions
  README.md               what each comparator pair checks
  DESIGN.md               how the pairs are built: vocabulary, bridges
  COMPARATOR_RUNS.md      the comparator pins and results
  <Pair>/                 Challenge.lean, SolutionBasic.lean, Solution.lean, comparator.json
  Support/                one bridge per pair, identifying the vocabulary with the library
ASSUMPTIONS.md            the cited results assumed, with their Lean statements (generated)
CORRESPONDENCE.md         paper to Lean, node by node
CERTIFICATE.md            generated record of the toolchain, the build and each node's axiom
                          closure
ledger/manifest.yaml      one row per registered statement: hash, paper source, state
paper/                    sandpile.tex, the paper pinned by the SHA-256 in ledger/manifest.yaml;
                          sandpile-arxiv.tex, the unmodified arXiv source, with arxiv/ holding
                          its bibliography and figures; CHANGES_FROM_ARXIV.md, the differences
                          between the two
tools/                    the checkers and generators listed under Building
.github/workflows/        the CI build and the comparator audit
formalization.yaml        the mathlib-initiative disclosure of models, tooling, cost and review
CITATION.cff              citation metadata
CONTRIBUTING.md           building notes and the elaboration policy for new files
LICENSE                   the Apache License 2.0
lakefile.lean, lake-manifest.json, lean-toolchain   the pinned build
```

## How this was built

The Lean code was written with AI assistance, using models from Anthropic (Claude) and
DeepSeek, under the direction of the author. Every proof is checked by the Lean kernel. The
models, tooling, cost and review status are disclosed in [`formalization.yaml`](formalization.yaml),
following the [mathlib-initiative](https://github.com/mathlib-initiative/formalization.yaml)
standard.

## Authors and citation

The Lean development is by **Ahmed Bou-Rabee**.  The paper it formalizes
(arXiv:2609.02829) is joint work of Ahmed Bou-Rabee and Christoforos
Panagiotis.  To cite the formalization, use [`CITATION.cff`](CITATION.cff).

This formalization is built on [Lean 4](https://lean-lang.org),
[Mathlib](https://github.com/leanprover-community/mathlib4) and the shared
library [`Lattice-Probability`](https://github.com/nitromannitol/Lattice-Probability);
the comparator audit in [`SandpileAudit/`](SandpileAudit/) is set up for
[`leanprover/comparator`](https://github.com/leanprover/comparator).

## License

The Lean code in this repository is licensed under the **Apache License 2.0**
(see [`LICENSE`](LICENSE)).  The paper source in `paper/` is included for
reference and is not covered by the Apache license.
