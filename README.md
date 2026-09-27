# Divisible-Sandpile-Percolation

A machine-checked **Lean 4** formalization of the paper
[*Quantitative explosion and percolation of the divisible sandpile*](https://arxiv.org/abs/2609.02829)
(Ahmed Bou-Rabee and Christoforos Panagiotis, arXiv:2609.02829), built on
[`mathlib`](https://github.com/leanprover-community/mathlib4) and the shared
library [`Lattice-Probability`](https://github.com/nitromannitol/Lattice-Probability)
(`LatticeProb`).

[![CI](https://github.com/nitromannitol/Divisible-Sandpile-Percolation/actions/workflows/build.yml/badge.svg)](https://github.com/nitromannitol/Divisible-Sandpile-Percolation/actions/workflows/build.yml)
[![Comparator audit](https://github.com/nitromannitol/Divisible-Sandpile-Percolation/actions/workflows/comparator.yml/badge.svg)](https://github.com/nitromannitol/Divisible-Sandpile-Percolation/actions/workflows/comparator.yml)

## What this is

The divisible sandpile on `ℤ^d` starts from an i.i.d. mass `σ(x)` at each site.
A site is unstable when its mass exceeds one; an unstable site topples, keeping
one unit and sharing the excess equally among its `2d` neighbours, and at each
discrete step every unstable site topples at once.  Writing `u_t(x)` for the
mass `x` has sent to each neighbour in the first `t` steps, `u_0 ≡ 0` and

    u_{t+1}(x) = ( (σ(x) − 1)/(2d) + (1/(2d)) Σ_{y∼x} u_t(y) )_+ .

At mean `ρ = E σ(0)` the sandpile either stabilizes at every site or explodes at
every site; it stabilizes for `ρ < 1` and explodes for `ρ = 1` with positive
finite variance.  The paper asks how fast it explodes at `ρ = 1`, and what the
toppled set `𝒯^{(ρ)} = {x : u_∞^{(ρ)}(x) > 0}` looks like for `ρ < 1`.

Theorem 1.1 says that for every `d ≥ 2`, under a uniform variance lower bound
and a uniform exponential moment along a family of laws, there is `ρ₊ < 1` such
that `𝒯^{(ρ)}` contains an infinite nearest-neighbour component almost surely
for every `ρ ∈ (ρ₊, 1)`: the toppled set percolates below mean one.  It follows
from Theorem 1.2, which gives an explicit percolating level set of the
finite-time odometer at mean one: for every `t` large,
`{x : u_t(x) > c h(t)}` contains an infinite component almost surely, with
`h(t) = t^{(4−d)/4}` for `d ∈ {2,3}`, `log t` for `d = 4` and `(log t)^{2/d}`
for `d ≥ 5`.  Theorem 1.3 collects the growth and scaling results at mean one:
the growth of `E u_t(0)` and the parabolic scaling limit to a Brownian
optimal-stopping value in `d ≤ 3`; the logarithmic growth, the first-order
determinism, the Gaussian fluctuations with variance `4 Var(ζ(0))/π²` and the
superdiffusive limit to the membrane model in `d = 4`; and in `d ≥ 5` the
first-order determinism, the tail-determined order `(log t)^{1/min{γ,d/2}}` of
the mean, the weighted membrane limits, and a scenery whose rescaled
fluctuations have uncountably many distinct subsequential limits.

This repository formalizes **every labelled theorem, lemma, proposition and
corollary of the paper**: 58 labelled statements, registered as 70 nodes
because a statement in several parts is registered one part per node
(Theorem 1.3 alone is ten nodes).  Not formalized: the proof-overview,
related-work and open-problem subsections, the unlabelled remarks (including
the nonpercolation remark at low mean, which quotes a Peierls argument of Fey,
Meester and Redig rather than proving one), and the figures.

**What is assumed.**  Results that the paper quotes from the literature are
stated in Lean as propositions in `Sandpile/External/`, and every theorem whose
proof uses one takes it as an explicit hypothesis, so the statement shows
exactly which of them it rests on.  There are **19** such propositions, **not
proved here**.  [`ASSUMPTIONS.md`](ASSUMPTIONS.md) lists all 19 with their
verbatim Lean statements.  They are random-walk estimates (the ball-killed
Green bounds, the local central limit theorem and its paired dimension-four
form), the crossing comparisons of
Köhler-Schindler and Tassion in planar and continuum form, Pitt's Gaussian FKG
inequality, the normal comparison inequality of Li and Shao, Gaussian
Lipschitz concentration, the Liggett-Schonmann-Stacey domination, optimal
stopping for Brownian motion and the stability of optimal-stopping values, the
occupation density of a Euclidean ball, the strong Markov property at the ball
exit time, a Besov tightness criterion, the compact negative-Sobolev
embedding, the four-dimensional membrane scaling limit, the multivariate
Berry-Esseen comparison, and Timár's exterior boundary connectivity.

Seven further results the paper cites without proof are **proved unconditionally
in this repository** (`Sandpile/External/*Proved.lean`) and so are not carried
as a hypothesis by any statement here: the `d ≥ 5` Green-function estimates,
the finite-time variance scale, the heat-kernel bounds, the discrete
optimal-stopping representation of the odometer, the determination of a
centred Gaussian law by its covariance, Pinsker's inequality, and the second
intersection moment of two independent walks.

- **No `sorry`** anywhere in the library.  (Each Mathlib-only comparator
  challenge in `Audit/` contains its single intentional statement-level
  `sorry`, filled by the corresponding solution file.)
- **No custom `axiom`.**  The main theorems reduce to `mathlib`'s three
  standard foundational axioms `propext`, `Classical.choice` and `Quot.sound`,
  verified by [`Sandpile/Meta/AxiomsAudit.lean`](Sandpile/Meta/AxiomsAudit.lean).
  The cited results above are hypotheses, not axioms.
- Pinned to Lean `v4.32.0`, `mathlib` at revision
  `81a5d257c8e410db227a6665ed08f64fea08e997` and `Lattice-Probability` at
  commit `bbe0b90`.

<!-- STATUS-BEGIN (generated by tools/sync_docs.py) -->

Status: **98 registered statements: 82 `SEALED`, proved here, and 16 `FROZEN`, cited results that are assumed.**  The 82 sealed nodes are machine-checked and no sealed node's
axiom closure contains `sorryAx`.  The 16 `FROZEN` nodes are cited results, stated in
`Sandpile/External/` and carried as explicit hypotheses by the theorems
that use them; they are assumed here, not proved.  Run
`python3 tools/check_axioms.py` to confirm.  Counts here are generated
from `ledger/manifest.yaml` by `python3 tools/sync_docs.py`; do not
edit them by hand and do not trust a count in prose that the checkers
have not confirmed.

<!-- STATUS-END -->

## Main results

The main theorems are stated in full in
[`Sandpile/MainTheorems.lean`](Sandpile/MainTheorems.lean), each proved by
`exact` of its certified counterpart in `Sandpile/Frozen/`, so the statements
displayed there are the certified ones.  The hypotheses listed are the cited
results each theorem carries; those marked † are also proved in this
repository and can be discharged.

* **`Sandpile.percolation_below_criticality`** (Theorem 1.1,
  `thm:main-nontriviality`): for `d ≥ 2` and a family of laws `μ_ρ` of mean
  `ρ`, with `Var_{μ_ρ} σ(0) ≥ ν₀²` and `E_{μ_ρ} e^{θ₀|σ(0)−ρ|} ≤ K₀` for
  `ρ ∈ [ρ₀, 1)`, there is `ρ₊ ∈ [ρ₀, 1)` such that for every `ρ ∈ (ρ₊, 1)` the
  toppled set contains an infinite component almost surely.  Hypotheses:
  `BallGreenBounds`, `PlanarRSW`, `LSSDomination`, `ExteriorBoundaryConnected`,
  `ContinuumRSW`, `PittGaussianFKG`, `BallOccupationDensity`, `LocalCLT`,
  `CubeStoppingStability`.
* **`Sandpile.critical_level_percolation`** (Theorem 1.2,
  `thm:main-critical-level-percolation`): there are `c > 0` and `t₀`, depending
  only on `d, ν₀, θ₀, K₀`, such that for every mean-one law with those bounds and
  every `t ≥ t₀`, `{x : u_t(x) > c h(t)}` contains an infinite component almost
  surely.  Hypotheses: those of Theorem 1.1 together with `GreenBoundsHigh`† and
  `VarianceScale`†.
* **`Sandpile.mean_growth_le_three`** (Theorem 1.3(i)(a)): in `d ≤ 3`,
  `t^{−(4−d)/4} E u_t(0)` converges to a positive limit.  Hypotheses:
  `LocalCLT`, `ContinuumStoppingStability`, `VarianceScale`†,
  `ContinuumOptimalStopping`.
* **`Sandpile.brownian_scaling_limit`** (Theorem 1.3(i)(b)): in `d ≤ 3`, the
  multilinear interpolation of `R^{−(2−d/2)} u_{⌊TR²⌋}` converges in
  finite-dimensional distributions to the Brownian stopping value `𝒰(T, ·)` and
  is tight in the uniform norm on compact sets.  Hypotheses: `LocalCLT`,
  `ContinuumStoppingStability`.
* **`Sandpile.mean_growth_four`** (Theorem 1.3(ii)(a), first clause): in
  `d = 4`, `c log t ≤ E u_t(0) ≤ C log t` for `t ≥ 2`.  No hypotheses.
* **`Sandpile.four_first_order`** (Theorem 1.3(ii)(a), second clause): in
  `d = 4`, `u_t(x)/E u_t(0) → 1` in `L²` and almost surely.  No hypotheses.
* **`Sandpile.four_gaussian`** (Theorem 1.3(ii)(b)): in `d = 4`,
  `(u_t(0) − E u_t(0))/√(log t)` converges in distribution to
  `N(0, 4 Var(ζ(0))/π²)`, and `Var(u_t(0))/log t` converges to the same
  constant.  Hypothesis: `PairedLocalCLTFour`†.
* **`Sandpile.four_sobolev`** (Theorem 1.3(ii)(c)): in `d = 4`, the centred
  fields at diffusive times are tight in `H^{−s}_loc`, and at the superdiffusive
  times `⌊R^α⌋`, `α > 2`, they converge modulo constants to the membrane model
  `𝒢_4`.  Hypotheses: `HeatKernelBounds`†, `VarianceScale`†,
  `ContinuumBesovTightness`, `MembraneScalingLimitFour`.
* **`Sandpile.high_first_order`** (Theorem 1.3(iii)(a)): in `d ≥ 5`,
  `u_t(x)/E u_t(0) → 1` in `L²` and almost surely, and
  `E u_t(0) ≥ c (log t)^{2/d}` for all large `t`.  Hypothesis:
  `GreenBoundsHigh`†.
* **`Sandpile.high_tail`** (Theorem 1.3(iii)(b)): in `d ≥ 5`, if
  `−log P(ζ(0) ≤ −s) ≍ s^γ` with `γ ≥ 1`, `γ ≠ d/2`, then
  `E u_t(0) ≍ (log t)^{1/min{γ,d/2}}`.  Hypothesis: `GreenBoundsHigh`†.
* **`Sandpile.high_sobolev_limit`** (Theorem 1.3(iii)(c)): in `d ≥ 5`, the
  fields `R^{(d−4)/2}(u_{⌊TR²⌋} − E u_{⌊TR²⌋}(0))^{(R)}` converge in
  `H^{−s}_loc`, `s > (d−4)/2`, to `ℋ_{1,T}` for Gaussian scenery and to
  `ℋ_{1−1/α,T}` for atomless scenery bounded above with a regularly varying
  lower tail of index `α > 2`.  Hypotheses: `HeatKernelBounds`†,
  `GreenBoundsHigh`†, `GaussianLipschitzConcentration`, `NormalComparison`,
  `IntersectionSecondMoment`†, `LocalCLT`, `ContinuumBesovTightness`.
* **`Sandpile.high_nonconvergence`** (Theorem 1.3(iii)(d)): in `d ≥ 5`, there
  is a law with mean zero, variance one, a smooth positive density and an
  exponential moment whose rescaled fluctuations are tight in `H^{−s}_loc` but
  have uncountably many distinct subsequential limits, and so do not converge.
  Hypotheses: `IntersectionSecondMoment`†, `LocalCLT`,
  `ContinuumBesovTightness`.

## Scope and faithfulness

Every labelled statement of the paper is registered: one Lean declaration per
theorem, lemma, proposition and corollary, or per part of one, and one
proposition per cited result.  A registered statement's text between the lines
`-- FROZEN-STATEMENT-BEGIN` and `-- FROZEN-STATEMENT-END` is pinned by the
SHA-256 of those bytes in [`ledger/manifest.yaml`](ledger/manifest.yaml),
together with the line range in `paper/sandpile.tex` and the `\label` it
transcribes; the proof after the end marker may be rewritten freely.  In the
manifest, a registered statement is `SEALED` when it is proved with an axiom
closure of exactly the three standard axioms, and `FROZEN` when it is a cited
result assumed rather than proved.  Every registered statement is pinned by
hash; only the `FROZEN` ones are assumed.  The paper transcribed is
`paper/sandpile.tex`, which is arXiv:2609.02829v1 with the corrections listed in
[`paper/CHANGES_FROM_ARXIV.md`](paper/CHANGES_FROM_ARXIV.md).

These words are used throughout with fixed meanings.

| term | meaning |
|---|---|
| **registered statement**, also called a **node** | one Lean declaration transcribing one statement of the paper, or one result the paper cites. Each has an entry in `ledger/manifest.yaml`. |
| **frozen statement** | the declaration's text between the lines `-- FROZEN-STATEMENT-BEGIN` and `-- FROZEN-STATEMENT-END`, pinned by the SHA-256 of those bytes. It cannot change without the change being recorded in the manifest. The proof after the end marker may be rewritten freely. |
| **`SEALED`** | the node is **proved** here: a complete proof, whose axiom closure contains only `propext`, `Classical.choice` and `Quot.sound`. |
| **`FROZEN`** | the node is **assumed**, not proved: a result the paper quotes from the literature, stated as a proposition in `Sandpile/External/` and carried as an explicit hypothesis by every theorem whose proof uses it. Every one is listed with its statement in [`ASSUMPTIONS.md`](ASSUMPTIONS.md). |
| **`DRAFT_SORRY`** | the statement is pinned but its proof is still open, registered as a `sorry`. |
| **cited input**, **external** | a `FROZEN` node, in the sense above. |
| **axiom closure** | the axioms a proof ultimately rests on, as reported by Lean's `#print axioms`. |
| **`sorryAx`** | the axiom Lean inserts for an unproved `sorry`; its presence in an axiom closure means the result is not proved. |

The word *frozen* carries two senses, so it is worth separating them: every
registered statement is frozen in the sense of being **pinned by hash**, while
the state `FROZEN` marks the subset that is **assumed rather than proved**.

Two checkers compare each Lean statement with the paper rather than with a hash.
`tools/check_clauses.py` counts the assertions of the paper statement and the
top-level conjuncts of the Lean conclusion, and requires a written reading of
every node saying what each side asserts.  `tools/check_exponents.py` extracts
the exponents from both sides and matches them, following the definitions a
Lean statement names; anything the paper has and Lean does not must be
explained per node or the check fails.  In each frozen statement whose
conclusion has a real existential constant, `tools/check_constants.py` checks
that no paper parameter is bound before it.

The paper-to-Lean map, node by node, is [`CORRESPONDENCE.md`](CORRESPONDENCE.md):
its conventions, the three standing conventions the Lean headers refer to by
name, the cited inputs of each node, every place where the form of a Lean
statement differs from the paper's, and a generated table of every registered
statement with its Lean name and paper location.  In outline, the places where
the form of a Lean statement differs from the paper's are these:

- The fields are fixed by their one-site law, through `centeredMassLaw d ν` or
  `massLaw d μ`; an i.i.d. field is determined by its one-site law.
- Mathlib has no Sobolev space, so every convergence in `H^{−s}_loc` is stated
  as convergence in distribution of each pairing to the matching centred
  Gaussian together with tightness of the `H^{−s}(D)` norms, and convergence in
  `C_loc` likewise with the uniform norm on compact sets.
- Mathlib constructs neither white noise nor Brownian motion, so both are
  predicates and each statement is quantified over a probability space carrying
  them; `Sandpile.Continuum.exists_isWhiteNoise` and
  `Sandpile.Continuum.exists_isBrownian` show that neither predicate is vacuous.
- An exponential-moment bound `E e^{θ₀|σ(0)−ρ|} ≤ K₀` is stated together with
  the integrability of the exponential, since the Bochner integral of a
  non-integrable function is zero.
- The infinite Green field is the limit of the finite-box partial sums rather
  than an unordered `tsum`; the crossing statements carry the paper's
  continuous-modification clause as an explicit almost-sure hypothesis, and the
  continuum crossing comparison is stated for a field on a probability space;
  and the continuum value is read off a modification of the Gaussian
  heat potential that is continuous and of polynomial growth on each finite
  strip.
- In Theorem 1.1 the threshold `ρ₊` is bound after the witnesses `ρ₀, ν₀, θ₀,
  K₀` and before `ρ`, the reading under which the paper's membership
  `ρ₊ ∈ [ρ₀, 1)` holds.

## Verified against a Mathlib-only statement

So that the main claims can be read without trusting the development, all
twelve main theorems are restated using **only Mathlib**, with no project or
library definitions, in `Audit/<Thm>/Challenge.lean`.  Each challenge rebuilds
from Mathlib primitives every definition the statement reaches: the lattice,
i.i.d. laws, the heat kernel and the Brownian exit time as in
`Lattice-Probability`; the odometer, the walk and its stopping problems; the
continuum kernels, Sobolev norms, white noise, Brownian motion and the Brownian
stopping values; the planar crossing events and continuum planar fields; and
the cited results it assumes.  It contains one intentional statement-level
`sorry`, which the corresponding `Solution.lean` fills from the library through
the bridges in `Audit/Support/`.  The configurations in
`Audit/*/comparator.json` are for
[`leanprover/comparator`](https://github.com/leanprover/comparator), which
confirms that the two statements have identical elaborated types and that the
proof reduces to the three standard axioms (see
[`Audit/README.md`](Audit/README.md)).

The twelve pairs are `Nontriviality`, `CriticalLevels`, `MeanGrowthLow`,
`BrownianScalingLimit`, `MeanGrowthFour`, `FourFirstOrder`, `FourGaussian`,
`FourSobolev`, `HighFirstOrder`, `HighTail`, `HighSobolevLimit` and
`HighNonconvergence`.  All twelve solutions build and depend only on
`propext`, `Classical.choice` and `Quot.sound`, and
`Audit/StatementRegression.lean` checks locally that each solution statement is
exactly the challenge statement and mentions no constant of `Sandpile` or
`LatticeProb`.  The comparator was run on all twelve pairs on 2026-09-24, at
commit `4545f0b`, and every pair passed with the Lean kernel and with the
independent nanoda kernel; the results and the reproduction steps are in
[`Audit/COMPARATOR_RUNS.md`](Audit/COMPARATOR_RUNS.md).  The workflow
[`.github/workflows/comparator.yml`](.github/workflows/comparator.yml) runs
the same check on request.

## Building

The project uses [`elan`](https://github.com/leanprover/elan) (the Lean
toolchain manager) and Lake.  The toolchain is pinned in
[`lean-toolchain`](lean-toolchain) (`leanprover/lean4:v4.32.0`), so `elan`
installs the right Lean version automatically, and the dependencies are pinned
to commits in `lakefile.lean` and [`lake-manifest.json`](lake-manifest.json);
`lake` fetches `Lattice-Probability` together with Mathlib.

```bash
lake exe cache get   # prebuilt Mathlib
lake build           # compile the project
```

```bash
lake build Sandpile.Meta.AxiomsAudit   # print the axioms of the twelve main theorems
lake build Audit                       # the comparator challenges and solutions
lake build Audit.StatementRegression
```

To use the library, `import Sandpile` pulls in the whole development; the main
results are in `import Sandpile.MainTheorems`.

The checkers in `tools/` need Python 3 and PyYAML (`pip install pyyaml`).
`check_axioms.py` and `check_warnings.py` run Lean; the others read the
manifest, the paper and the Lean sources.

| command | what it guarantees |
|---|---|
| `python3 tools/check_manifest.py` | every node's file holds exactly one frozen block whose SHA-256 equals `frozen_sha256` and which declares exactly the node's `export`; every file in `Sandpile/Frozen/` belongs to one node; `Sandpile/` and `Sandpile.lean` contain no `axiom`, `admit` or `sorryAx`, and `sorry` occurs only in files of `DRAFT_SORRY` nodes (none is registered) |
| `python3 tools/check_axioms.py` | runs `#print axioms` on every manifest export; each closure is its registered one, and none contains `sorryAx` |
| `python3 tools/check_warnings.py` | runs `lake build Sandpile` and fails if it emits any Lean warning other than one `declaration uses 'sorry'` per `DRAFT_SORRY` node |
| `python3 tools/check_constants.py` | in a frozen statement whose conclusion has a real existential constant, no paper parameter is bound before it |
| `python3 tools/check_coverage.py` | every labelled theorem, lemma, proposition and corollary of `paper/sandpile.tex` is named in the `source` of some manifest node |
| `python3 tools/check_clauses.py` | compares the assertion count of each paper statement with the conjunct count of its Lean statement, and requires a recorded reading of every node |
| `python3 tools/check_exponents.py` | compares the exponents written in a paper statement with those in its Lean statement and the definitions it names |
| `python3 tools/check_progress.py` | counts the open holes in the tree against the baseline in `ledger/holes.json` |

Also in `tools/`: `paper_anchors.py` and `paper_citations.py` check the
`sandpile.tex:<lines>` ranges in the manifest and in the Lean docstrings
against the paper's labels; `sync_docs.py` checks (`--write` regenerates) the
status block of this file and the registered-statements table of
`CORRESPONDENCE.md`; `assumptions.py` regenerates `ASSUMPTIONS.md` (`--check`
verifies it is current); `certificate.py` regenerates `CERTIFICATE.md`;
`freeze.py` registers or refreshes a node in the manifest.

## Repository layout

```
Sandpile/
  MainTheorems.lean   the main theorems, stated in full
  Frozen/             the certified statement surface, one frozen statement per file
  External/           the cited results, each a frozen Prop; the *Proved.lean files prove six
  Support/            the paper-specific definitions and lemmas the frozen statements are proved
                      from; general probability and analysis (Efron–Stein, smooth maxima,
                      weighted CLT, Taylor comparison, Laplace and exponential-moment bounds,
                      Gaussian tails, Sobolev norms) are imported from Lattice-Probability
  Continuum/          white noise, Brownian motion, the continuum fields and stopping values
  Meta/               AxiomsAudit.lean
  Basic.lean          the odometer, its limit, the toppled set, the mass law
  Law.lean            the centred mass law and the mean odometer
  Walk.lean           the heat and Green kernels, the walk and its stopping problems
Sandpile.lean         the root module (imports the whole library)
Audit/                Mathlib-only comparator challenges and solutions
ASSUMPTIONS.md        the cited results assumed, with their Lean statements (generated)
CORRESPONDENCE.md     paper ↔ Lean, node by node
CERTIFICATE.md        generated record of the toolchain, the build and each node's axiom closure
ledger/manifest.yaml  one row per registered statement: hash, paper source, state
ledger/holes.json     the open-hole baseline of tools/check_progress.py
paper/sandpile.tex    the paper, pinned by the SHA-256 in ledger/manifest.yaml
paper/sandpile-arxiv.tex  the unmodified arXiv source (paper/arxiv/: its bibliography and figures)
paper/CHANGES_FROM_ARXIV.md  the differences between the two
tools/                the checkers and generators listed under Building
```

## How this was built

The Lean code in this repository was written by AI models under the
supervision of the author, over 1007 commits between 2026-09-06 and
2026-09-23. A supervising Claude Code session set up the frozen-statement
scaffold, carried out the author's decisions and merged the agents' branches. Claude
Opus generals, running as Claude Code subagents in shifts from 2026-09-10,
wrote much of the continuum and tightness chain, the dimension greater than
four linearization and many-limits chain, the killed scaling remark and the
assembly of the main theorems; the records call them Opus generals and do not
name the model version. OpenAI's gpt-6-astra, through Codex, worked the
dimension-four chain (2026-09-07) and, in later runs, repaired the
limiting-crossing, stopping and white-noise work and wrote the fourth version
of the crossing statement (2026-09-12). DeepSeek-v4.1-flash generals, run by a
custom API driver, worked the continuum, crossing, linearization, dimension
greater than four and Brownian ball chains (2026-09-11 to 2026-09-15), and
DeepSeek-v4.1-flash and GLM-5.3-flash agents drafted compile-filtered
candidates for short proof bodies. GLM-5.3 generals worked the percolation and
linearization chain and the growth chain. From 2026-09-16 Claude Sonnet
generals, launched through Claude Code, continued the many-limits, Brownian
ball, crossing, growth and Theorem 1.3 work; the records do not name the
Sonnet version. A Kimi Code agent (kimi-code/k3-256k) worked on Theorem
1.3(i)(b) on a separate branch that was not merged. Claude Opus 5.5 wrote
`Sandpile/MainTheorems.lean`, the comparator surface in `Audit/` and the
release documentation. The models, tooling, cost, and review status are
disclosed in full in [`formalization.yaml`](formalization.yaml), following the
[mathlib-initiative](https://github.com/mathlib-initiative/formalization.yaml)
standard.

## Authors and citation

The Lean development is by **Ahmed Bou-Rabee**.  The paper it formalizes is
joint work of Ahmed Bou-Rabee and Christoforos Panagiotis.  If you use this
formalization, please cite it using the metadata in
[`CITATION.cff`](CITATION.cff).

## Acknowledgements

This formalization is built on [Lean 4](https://lean-lang.org),
[Mathlib](https://github.com/leanprover-community/mathlib4) and the shared
library [`Lattice-Probability`](https://github.com/nitromannitol/Lattice-Probability);
the comparator audit in [`Audit/`](Audit/) is set up for
[`leanprover/comparator`](https://github.com/leanprover/comparator).

## License

The Lean code in this repository is licensed under the **Apache License 2.0**
(see [`LICENSE`](LICENSE)).  The paper source in `paper/` is included for
reference and is not covered by the Apache license.
