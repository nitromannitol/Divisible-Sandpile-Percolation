# Correspondence: paper ↔ Lean

Maps every frozen declaration to *Quantitative explosion and percolation of the
divisible sandpile* (Bou-Rabee–Panagiotis).

## Conventions

- The paper is pinned at `paper/sandpile.tex`; its SHA-256 is in
  `ledger/manifest.yaml`.  Source locations are `sandpile.tex:<line range>` plus
  the LaTeX `\label` name.  Never cite an equation numeral.
- The bytes between `-- FROZEN-STATEMENT-BEGIN` and `-- FROZEN-STATEMENT-END`
  are the contract.  `python3 tools/check_manifest.py` is the authority on the
  hash recipe.

## Standing conventions

Three conventions are applied throughout and are referred to by name in the Lean
headers.

- **R1.**  A result the paper's proof quotes from another paper is not proved
  here.  It is stated as a proposition in `Sandpile/External/`, frozen like a
  paper statement, and attached to every theorem whose proof uses it as an
  explicit hypothesis, and nothing more.
- **R2.**  When a Lean definition would return a junk value on inputs the paper
  never considers (the Bochner integral of a non-integrable function is zero,
  a supremum over an unbounded set is zero), the clause that rules those inputs
  out is conjoined to the statement rather than left implicit, so that the junk
  value cannot stand for a hypothesis or for a conclusion.
- **R4.**  Where a definition could be read in two ways, the reading the paper's
  proof uses is fixed explicitly in the statement rather than left to the
  reader, so that a silent choice cannot make a statement vacuous.

## Main results

The main results are additionally exposed, stated in full, in
[`Sandpile/MainTheorems.lean`](Sandpile/MainTheorems.lean), each proved by
`exact` of its certified statement, and all twelve are restated over a
Mathlib-only vocabulary for the comparator (see [`Audit/`](Audit/)).

| Source | Main theorem | Certified statement | Comparator |
|---|---|---|---|
| Theorem 1.1, `thm:main-nontriviality` | `Sandpile.percolation_below_criticality` | `Sandpile.Frozen.percolation_below_criticality` | `Audit/Nontriviality/` |
| Theorem 1.2, `thm:main-critical-level-percolation` | `Sandpile.critical_level_percolation` | `Sandpile.Frozen.critical_level_percolation` | `Audit/CriticalLevels/` |
| Theorem 1.3(i)(a), `thm:main-explosion` | `Sandpile.mean_growth_le_three` | `Sandpile.Frozen.mean_growth_le_three` | `Audit/MeanGrowthLow/` |
| Theorem 1.3(i)(b), `thm:main-explosion` | `Sandpile.brownian_scaling_limit` | `Sandpile.Frozen.brownian_scaling_limit` | `Audit/BrownianScalingLimit/` |
| Theorem 1.3(ii)(a), first clause, `thm:main-explosion` | `Sandpile.mean_growth_four` | `Sandpile.Frozen.mean_growth_four` | `Audit/MeanGrowthFour/` |
| Theorem 1.3(ii)(a), second clause, `thm:main-explosion` | `Sandpile.four_first_order` | `Sandpile.Frozen.four_first_order` | `Audit/FourFirstOrder/` |
| Theorem 1.3(ii)(b), `thm:main-explosion` | `Sandpile.four_gaussian` | `Sandpile.Frozen.four_gaussian` | `Audit/FourGaussian/` |
| Theorem 1.3(ii)(c), `thm:main-explosion` | `Sandpile.four_sobolev` | `Sandpile.Frozen.four_sobolev` | `Audit/FourSobolev/` |
| Theorem 1.3(iii)(a), `thm:main-explosion` | `Sandpile.high_first_order` | `Sandpile.Frozen.high_first_order` | `Audit/HighFirstOrder/` |
| Theorem 1.3(iii)(b), `thm:main-explosion` | `Sandpile.high_tail` | `Sandpile.Frozen.high_tail` | `Audit/HighTail/` |
| Theorem 1.3(iii)(c), `thm:main-explosion` | `Sandpile.high_sobolev_limit` | `Sandpile.Frozen.high_sobolev_limit` | `Audit/HighSobolevLimit/` |
| Theorem 1.3(iii)(d), `thm:main-explosion` | `Sandpile.high_nonconvergence` | `Sandpile.Frozen.high_nonconvergence` | `Audit/HighNonconvergence/` |

## How the paper's objects are modelled

| paper | Lean | where |
|---|---|---|
| `u_t`, the odometer driven by the masses `σ` | `Sandpile.odometer` | `Sandpile/Basic.lean` |
| `u_t`, written in the scenery `ζ` | `Sandpile.odometerOf` | `Sandpile/Walk.lean` |
| `ζ = (σ - 1)/(2d)` | `Sandpile.scenery` | `Sandpile/Walk.lean` |
| `P`, the averaging operator | `Sandpile.avg` | `Sandpile/Walk.lean` |
| `V_t`, the membrane field | `Sandpile.membrane` | `Sandpile/Walk.lean` |
| `p_k`, `g_t`, `G` | `Sandpile.heatKernel`, `greenTime`, `green` | `Sandpile/Walk.lean` |
| `g_t^D`, `g^D`, `τ_D` | `Sandpile.killedGreenTime`, `killedGreen`, `exitTime` | `Sandpile/Walk.lean` |
| simple random walk from `x` | `Sandpile.walkLaw d x` on `ℕ → Site d` | `Sandpile/Walk.lean` |
| `sup_{τ ≤ n} E_x[…]` | `Sandpile.stoppingSup` | `Sandpile/Walk.lean` |
| `v_n`, `u_t^D` | `Sandpile.stoppingValue`, `localizedOdometer` | `Sandpile/Walk.lean` |
| `p_t^{BM}`, `g_t^{BM}` | `Sandpile.Continuum.heatKernelBM`, `greenTimeBM` | `Sandpile/Continuum/Kernel.lean` |
| `C_c^∞(D)`, `‖·‖_{H^s}`, `‖·‖_{H^{-s}(D)}` | `IsTestFn`, `sobolevNormSq`, `negSobolevNorm` | `Sandpile/Continuum/Sobolev.lean` |
| `f^{(R)}(z) = f(⌊Rz⌋)`, `f^{(R)}(φ)` | `embed`, `latticePairing` | `Sandpile/Continuum/Sobolev.lean` |
| white noise `𝒲`, the field `Z` | `IsWhiteNoise`, `gaussianPotential` | `Sandpile/Continuum/WhiteNoise.lean` |
| `𝒢_{d,T}`, `ℋ_{κ,T}`, `𝒢_4`, `F^ω` | `weightedMembraneCov` (at `κ = 0` and general `κ`), `membraneCov4`, `omegaRep` | `Sandpile/Continuum/Membrane.lean` |
| `⟹ … in H^{-s}_loc`, tightness in `H^{-s}_loc` | `TendstoInNegSobolev`, `TightInNegSobolev` | `Sandpile/Continuum/Membrane.lean` |
| Brownian motion with generator `Δ/(2d)`, `𝒟_h`, `𝒰_h`, `𝒰_{h,A}` | `IsBrownian`, `brownianDiscount`, `brownianValue`, `brownianValueBall` | `Sandpile/Continuum/Stopping.lean` |

### Where the form of a Lean statement differs from the paper's

The paper is `paper/sandpile.tex`, the arXiv version with the corrections listed in
[`paper/CHANGES_FROM_ARXIV.md`](paper/CHANGES_FROM_ARXIV.md).  The rows below
record how its statements are encoded in Lean.

| paper | how the Lean statement differs | why |
|---|---|---|
| `thm:main-nontriviality`, the threshold `ρ₊` | `ρPlus` is bound after the witnesses `ρ₀`, `ν₀`, `θ₀`, `K₀` and before `ρ` | the paper writes `ρ₊ = ρ₊(d,(μ_ρ)) ∈ [ρ₀,1)`.  The membership forces `ρ₀ ≤ ρ₊`, so the threshold cannot be independent of `ρ₀`: for a valid witness `ρ₀'` above a witness-independent `ρ₊` the paper's own membership claim would fail.  The dependence the theorem's content rests on is the one the Lean statement does express, that `ρ₊` is fixed before the density `ρ` it is a threshold for |
| `thm:main-explosion` and everything in the `ζ` language | the field is fixed by its one-site law, through `centeredMassLaw d ν` or `LatticeProb.iidLaw d ν` | the paper's fields are i.i.d., and an i.i.d. field is determined by its one-site law |
| every `⟹ … in H^{-s}_loc(ℝ^d)` | two clauses: convergence in distribution of each pairing to the matching centred Gaussian, and tightness of the `H^{-s}(D)` norms | Mathlib 4.32 has no Sobolev space; for a limit that is Gaussian and a family linear in the test function, Cramér-Wold makes the pair equivalent to the paper's assertion |
| every `⟹ … in C_loc` | the same pair, with the uniform norm on compact sets in place of the `H^{-s}` norm | same reason |
| white noise, Brownian motion | predicates, with each statement quantified over a probability space carrying the objects | Mathlib 4.32 constructs neither; there is no Kolmogorov extension theorem in it.  Neither predicate is vacuous any longer: `Sandpile.Continuum.exists_isWhiteNoise` builds a space carrying such a family from the isonormal process over a countable orthonormal basis of `L²(ℝ^d)`, and `Sandpile.Continuum.exists_isBrownian` builds one carrying the whole family of Brownian motions indexed by the starting point, from `d` independent copies of a real Brownian motion scaled by `1/√d`.  The statements quantify over a family indexed by the starting point on ONE space, which is what the construction supplies, since the starting point enters only as a translation |
| `lem:reflection-increment`, "concave in `t`" | the increments are nonincreasing | that is what the paper's proof establishes and what the rest of the paper uses |
| every node assuming `E e^{θ₀|ζ(0)|} ≤ K₀`, that is `thm:main-nontriviality`, `thm:main-critical-level-percolation`, `lem:weighted-exp-conc` (b), (c), (d), `thm:critical-toppling-d4`, `thm:d23-critical-level-percolation`, `thm:d4-ball-green-crossing`, `thm:d4-critical-level-percolation`, `lem:d4-exit-average-concentration`, `lem:dgt4-cascade`, `lem:dgt4-level-shift-decoupling`, `lem:dgt4-localization` and `thm:dgt4-nontriviality` | the exponential-moment bound is stated together with integrability of the exponential, as the paper's `K₀ < ∞` requires | the Bochner integral of a non-integrable nonnegative function is zero, so the bound alone holds for every law with no exponential moment |
| `lem:odometer-derivative`, `lem:difference-representation` | the optimal-stopping representation is an explicit hypothesis | their paper proofs cite it, and in this repository it is a cited result rather than a theorem, exactly as in `thm:RW` |
| planar conclusions (`thm:d23-critical-level-percolation`, `thm:d4-critical-level-percolation`) | an infinite component of `ℤ²`, pulled back along the embedding of the coordinate plane | the paper's crossings all live inside the plane, so this is the statement its proof gives |
| `eq:dgt4-infinite-green-field`, `V_∞` | the infinite Green field is the limit of the finite-box partial sums along the boxes (`Sandpile.Support.InfiniteGreenField`), zero where the limit does not exist, not an unordered real `tsum` | modelling decision: the Gaussian Green series is not absolutely summable, so the unordered `tsum` is zero and the field vanishes; the box limit exists in `L²` and almost surely for the Gaussian scenery, which is the field the paper uses |
| `prop:fixed-scale-crossings`, `lem:finite-scale-extraction` | the white-noise hypothesis carries the continuous-modification clause of `sandpile.tex:2111`: almost-sure continuity of `u ↦ X_s(u)` for the scales the paper defines, `0 < s ≤ 1` | modelling decision: the paper's crossings are of the continuous modification's level sets, and the modification exists only up to a null set, so the clause is an explicit hypothesis in its almost-sure form |
| the continuum crossing comparison `External.ContinuumRSW`, and with it `prop:fixed-scale-crossings`, `lem:finite-scale-extraction`, `thm:limiting-odometer-crossing` | the comparison is stated for a field on a probability space, with measurable coordinates and almost surely continuous sample paths, symmetric in law and with positively associated finite-dimensional distributions, and the crossing probabilities are the outer measures of subsets of that space; the rectangles are unchanged | modelling decision: stated for a law on the space of ALL planar functions, the comparison is empty, because a set measurable for the product σ-algebra is determined by countably many points and a horizontal line through the rectangle misses all of them, so every crossing event there has outer measure one (`Sandpile.Support.oldContinuumRSW_holds`) |
| `thm:main-explosion`(i)(b), the interpolated field; `thm:main-explosion`(iii)(c)-(d), the rescaled fluctuation | `Sandpile.Continuum.multilinearInterp` and `Sandpile.Continuum.diffusiveFluctuation` are defined in `Sandpile/Support/ExplInterp.lean` and `Sandpile/Support/ExplFluctuation.lean`, not beside the statements that use them | a definition stated in a `Frozen` file forces every support module that names it to import that file, and then the theorem in it can never be proved from those modules; the two definitions are unchanged, and the frozen blocks that name them are unchanged |
| `prop:continuum-value-selfsimilar` | the value is built from a modification `Z` of the Gaussian heat potential, almost surely continuous on `[0,T] × ℝ^d` and of polynomial growth there for every `T > 0`, and the stopping input `External.ContinuumOptimalStopping` is an explicit hypothesis; the three clauses keep their shape | modelling decision: the paper fixes the locally continuous modification at `sandpile.tex:1020-1021` and says "throughout `Z` denotes that version", and the raw `gaussianPotential` of an arbitrary white-noise family has no joint regularity, so the stopping value read off it is a junk value; the modification is what makes the two transfers of `sandpile.tex:1985-1993` legitimate |
| `cor:dlt4-mean-asymptotic`, `thm:main-explosion`(i)(b) | the limiting value is built from the same modification `Z` of the Gaussian heat potential as `prop:continuum-value-selfsimilar`, carried by the binders `Z`, `hZmod`, `hZcont` and `hZgrow` in that proposition's form and position; every conclusion keeps its shape | modelling decision: the paper fixes the continuous version at `sandpile.tex:1019-1021` and `sandpile.tex:2104` and writes `Z` for it throughout the subsection, and it is continuity on the strip together with polynomial growth there that makes the supremum over the Brownian stopping rules a supremum over a bounded set of reals |
| `prop:continuum-value-selfsimilar`, `cor:dlt4-mean-asymptotic`, `thm:main-explosion`(i)(b) | the polynomial-growth clause of the modification is quantified almost surely, the constants `C` and `k` bound after the sample point | modelling decision: the potential is a centred Gaussian at each point of the strip, so the envelope of a sample path over the strip is a random quantity and the constants are read off the path; the argument that consumes the clause, `Sandpile.Support.bddAbove_farValues_of_growth_pointwise`, takes the bound at a fixed sample point |
| `prop:continuum-value-selfsimilar`, `cor:dlt4-mean-asymptotic`, the rescaled odometer and the continuum value | `Sandpile.Continuum.rescaledOdometer` and `Sandpile.Continuum.continuumValue` are defined in `Sandpile/Support/MeanAValue.lean`, not beside the statements that read them | modelling decision, for the reason already recorded for `multilinearInterp`: a definition stated in a `Frozen` file forces every support module that names it to import that file, and then the theorem in it can never be proved from those modules; the definitions are unchanged |
| the field `Z` of `sandpile.tex:1014-1021` | the modification of the Gaussian heat potential that is almost surely continuous on every strip `[0,T] × ℝ^d`, and its polynomial growth on every strip, are both CONSTRUCTED, as `Sandpile.Support.exists_continuous_version` and `Sandpile.Support.continuousVersionGrowth`; no external input remains for this field | the increment of the potential is a centred Gaussian whose variance is the `L²` increment of the finite-time Brownian Green kernel, that increment is Hölder of exponent a quarter in the space-time distance on every strip, and a moment of order `8(d+2)` therefore satisfies the Kolmogorov condition with exponent `d+2`, above the `d+1` of the index space; the growth is Borel-Cantelli over the unit boxes of the integer lattice against the polynomial box tail of a quantitative Kolmogorov criterion, transferred from the constructed version to every almost-surely-continuous modification by their almost-sure pointwise agreement on a countable dense subset of the strip |


The planar RSW comparison is registered as `External.PlanarRSW`, the
integer lattice site specialization of Köhler-Schindler–Tassion Theorem 1
and Comment 1, cited at `sandpile.tex:400,2064,2218,2235`. Its universal
increasing homeomorphism is chosen before the law, scale and level.
Translation invariance converts the source’s centered rectangles to the
origin-anchored rectangles used here. The field’s symmetry and positive
association are explicit hypotheses of this input; it contains no Gaussian
mean or tail estimate. The square estimate and planar duality are proved in
`Support/GaussianSquareMean.lean` and `Support/RectangleIntersection.lean`.

The continuum crossing comparison is registered as `External.ContinuumRSW`, the
continuum form of Köhler-Schindler–Tassion Theorem 1 and Comment 1 that the
paper applies at `sandpile.tex:2235-2240`, and Pitt's Gaussian FKG theorem as
`External.PittGaussianFKG`, cited at `sandpile.tex:2104` for the association of
the finite collections.  Both are stated on a field carried by its probability
space.  What a crossing statement of that kind can and cannot say is settled in
`Sandpile/Support/CrossUnion.lean`: the outer measure of a crossing of an almost
surely continuous field lies between the measures of the chain events
`crossApprox` at the level and at any lower level, and those are genuine events
depending on countably many values of the field.  The old form of the comparison
and the proof that it was empty are kept in `Sandpile/Support/CrossVacuity.lean`.

## Nodes carrying cited inputs as hypotheses

A frozen statement whose paper proof cites a result the paper does not prove
takes that result as an explicit hypothesis.  The cited results are the `Prop`s
of `Sandpile/External/`; none of them is an axiom, and each is a row in the
program's external-debt ledger.  The attribution below is the paper's own: the
proof of the node cites the displayed estimate, by its equation label.

| node | cited input it assumes | which displays of the paper |
|---|---|---|
| `lem-dgt4-blocking-to-crossing` | `External.ExteriorBoundaryConnected` | Timár Theorem 3, cited at `sandpile.tex:6595` |
| `prop-fixed-scale-crossings` | `External.ContinuumRSW` | the continuum form of the RSW theorem of Köhler-Schindler and Tassion, cited at `sandpile.tex:2218` and applied at `sandpile.tex:2235-2240` |
| `prop-fixed-scale-crossings` | `External.GaussianLawDeterminedByCovariance` | the invariance in law of `𝒳_1` under the plane symmetries asserted at `sandpile.tex:2103-2104`, whose proof from the covariance identity of `Sandpile/Support/CrossBallSym.lean` needs the classical determination of a centred Gaussian law by its covariance. Carried at present by the support assembly `Sandpile.Support.fixed_scale_crossings_ball`; it is attached to the frozen statement when the node is sealed.  The shared library has since PROVED it, and `Sandpile/External/GaussianLawCovarianceProved.lean` discharges the Prop, so the dependents are unconditional |
| `prop-fixed-scale-crossings` | `External.PittGaussianFKG` | Pitt's Gaussian FKG theorem, cited at `sandpile.tex:2104` and applied at `sandpile.tex:2229` to build the circuit out of four rectangle crossings. Added at version 5, together with the same hypothesis on `lem-finite-scale-extraction` (version 5) and `thm-limiting-odometer-crossing` (version 6), which reach it through the fixed-scale proposition |
| `prop-fixed-scale-crossings` | `External.Pinsker` | Pinsker's inequality, cited by name at `sandpile.tex:2390` for the last step of the level loss. Carried at present by `Sandpile.Support.level_loss_of_entropy`.  The shared library has since PROVED it, and `Sandpile/External/PinskerProved.lean` discharges the Prop, so the dependents are unconditional |
| `lem-finite-scale-extraction` | `External.ContinuumRSW` | the same, reached through the rescaled crossing estimate of `sandpile.tex:2429-2436`, which is `prop:fixed-scale-crossings` rescaled. Added at version 3 |
| `lem-finite-scale-extraction` | `External.PittGaussianFKG` | the same, reached through `prop:fixed-scale-crossings`. Added at version 5 |
| `thm-limiting-odometer-crossing` | `External.ContinuumRSW` | the same, reached through `lem:finite-scale-extraction`, which the proof at `sandpile.tex:2531-2560` applies. Added at version 2 |
| `thm-limiting-odometer-crossing` | `External.PittGaussianFKG` | the same, reached through `lem:finite-scale-extraction`. Added at version 6 |
| `thm-rw`, `lem-odometer-derivative`, `lem-difference-representation` | `External.OptimalStopping` | the optimal-stopping representation, `thm:RW` |
| `cor-mean-localization` | `External.HeatKernelBounds` | `eq:rw-max-displacement` |
| `prop-d4-diffusive-tightness` | `External.HeatKernelBounds` | `eq:rw-gaussian-upper` |
| `prop-d4-superdiffusive-limit` | `External.HeatKernelBounds` | `eq:rw-tv-gradient` |
| `thm-d4-ball-green-crossing` | `External.PlanarRSW` | Kohler-Schindler–Tassin Theorem 1 and Comment 1, cited at `sandpile.tex:400,2064,2218,2235`; dimension 4 in the RSW framework at `sandpile.tex:661-663` |
| `thm-d4-critical-level-percolation` | `External.PlanarRSW` | rectangle extension of the Gaussian far field, cited at `sandpile.tex:3987` via Theorem `thm:d4-ball-green-crossing` |
| `thm-d4-critical-level-percolation` | `External.LSSDomination` | Liggett-Schonmann-Stacey Corollary 1.4, cited at `sandpile.tex:3987` |
| `thm-main-critical-level-percolation` | `External.PlanarRSW` | the `d = 4` branch, through `thm:d4-critical-level-percolation`, whose proof cites the rectangle extension of the Gaussian far field at `sandpile.tex:3987` |
| `thm-main-critical-level-percolation` | `External.LSSDomination` | the `d = 2,3` and `d = 4` branches, through `thm:d23-critical-level-percolation` and `thm:d4-critical-level-percolation`, whose proofs cite Liggett-Schonmann-Stacey Corollary 1.4 at `sandpile.tex:2589` and `sandpile.tex:3987` |
| `thm-main-critical-level-percolation` | `External.ExteriorBoundaryConnected` | the `d ≥ 5` branch, through `thm:dgt4-nontriviality`, whose proof cites Timar Theorem 3 at `sandpile.tex:6595` |
| `thm-dgt4-diffusive-membrane` | `External.HeatKernelBounds`, `External.GreenBoundsHigh`, `External.LocalCLT`, `External.ContinuumBesovTightness` | the same four, reached through `prop:weighted-membrane-limit`, which the proof at `sandpile.tex:4634-4686` applies with the weight `(1-r/T)^κ`. Added at version 2 |
| `prop-weighted-membrane-limit` | `External.HeatKernelBounds`, `External.GreenBoundsHigh`, `External.LocalCLT`, `External.ContinuumBesovTightness` | `eq:rw-gaussian-upper`, `eq:dgt4-intersection-first-moment`, `eq:lclt-parity`; and the Besov tightness criterion through `lem:sobolev-tightness`, which the tightness half of the proof applies. The last was added at version 3, when the tightness half was assembled |
| `thm-dgt4-height-lower` | `External.GreenBoundsHigh` | `eq:dgt4-green-tail`, `eq:dgt4-green-l2` |
| `lem-dgt4-localization` | `External.GreenBoundsHigh` | `eq:dgt4-green-tail` |
| `lem-dgt4-origin-frozen` | `External.GreenBoundsHigh` | `eq:dgt4-green-tail` |
| `lem-dgt4-smoothed-odometer-tail` | `External.GreenBoundsHigh` | `eq:dgt4-tail-kernel` |
| `lem-dgt4-path-survival` | `External.GreenBoundsHigh` | `eq:dgt4-intersection-first-moment` |
| `lem-dgt4-path-survival` | `External.NormalComparison` | Li and Shao Corollary 2.1, cited at `sandpile.tex:5507` for Step 1 of the proof in the Gaussian branch. Added at version 4 |
| `lem-dgt4-linearization-from-survival` | `External.GreenBoundsHigh` | `eq:dgt4-intersection-first-moment`, whose walk form is proved from it |
| `lem-dgt4-linearization-from-survival` | `External.IntersectionSecondMoment` | `eq:dgt4-intersection-second-moment`, cited from Lawler at `sandpile.tex:1324-1336` and used through `eq:dgt4-tested-intersection-moments`. Added at version 3 |
| `lem-dgt4-linearization-from-survival` | `External.ContinuumBesovTightness` | the Besov tightness criterion through `lem:sobolev-tightness`, which the `H^{-s}_loc` clause of the proof applies at `sandpile.tex:5845-5849`. Added at version 3 |
| `prop-dgt4-linearization` | `External.GreenBoundsHigh`, `External.NormalComparison`, `External.IntersectionSecondMoment`, `External.ContinuumBesovTightness` | the four cited results the proof at `sandpile.tex:5848-5859` reaches through `lem:dgt4-path-survival` and `lem:dgt4-linearization-from-survival`, which it applies to the time weights `(1-j/(R^2T))^k`. Added at version 2 |
| `prop-dgt4-contact-asymptotics` | `External.GreenBoundsHigh` | `eq:dgt4-green-tail`, `eq:dgt4-green-l2`, `eq:dgt4-tail-kernel`, `eq:dgt4-intersection-first-moment` |
| `prop-dgt4-contact-asymptotics` | `External.GaussianLipschitzConcentration` | Gaussian concentration for the Lipschitz functional `\Theta_n` of Step 4 of case (a), cited at `sandpile.tex:5262-5266`. Added at version 3 |
| `thm-dgt4-diffusive-membrane` | `External.GaussianLipschitzConcentration` | the same, through the theorem's second conjunct `prop:dgt4-contact-asymptotics`. Added at version 4 |
| `lem-d4-exit-average-concentration` | `External.BallGreenBounds` | `eq:d4ball-point` |
| `thm-d4-ball-green-crossing` | `External.BallGreenBounds` | `eq:d4ball-square`, `eq:d4ball-near`, `eq:d4ball-far-cube`, `eq:d4ball-shift` |
| `thm-d4-critical-level-percolation` | `External.BallGreenBounds` | `eq:d4ball-time-tail` |
| `lem-d4-double-heat-kernel` | `External.LocalCLT`, `External.PairedLocalCLTFour` | `eq:lclt-parity` and its quantitative paired remainder from Lawler–Limic Theorem 2.1.3, Eq. (2.8), used in `sandpile.tex:1171-1172` |
| `thm-main-explosion-i-a` | `External.LocalCLT` | Lawler–Limic Theorem 2.1.3, Eq. (2.8), cited at `sandpile.tex:1145-1161`, through the parabolic scaling limit `thm:main-explosion`(i)(b). |
| `thm-main-explosion-i-a` | `External.ContinuumStoppingStability` | reached through `cor:dlt4-mean-asymptotic` and `thm:main-explosion`(i)(b), which the proof applies at `T = 1`; the paper's own reduction is `sandpile.tex:299`, "Part (i)(a) is Corollary~\ref{cor:dlt4-mean-asymptotic}". Added at version 3, taken at the universe of the realization spaces the statement builds for itself at version 4 |
| `thm-main-explosion-i-a` | `External.VarianceScale` | reached through `prop:continuum-value-selfsimilar` (`sandpile.tex:1961-1980`), whose uniform exponential moment is the input the corollary's sentence names at `sandpile.tex:2030-2032`. Added at version 3 |
| `thm-main-explosion-i-a` | `External.ContinuumOptimalStopping` | Peskir and Shiryaev Theorem 2.2, cited at `sandpile.tex:1099`, reached through `prop:continuum-value-selfsimilar`. The statement names no probability space, so the hypothesis is carried for every space carrying a family of Brownian motions, which is the form the cited theorem has. Added at version 3 |
| `prop-dlt4-heat-potential-invariance` | `External.LocalCLT` | `eq:lclt-parity` |
| `thm-main-explosion-ii-c` | `External.ContinuumBesovTightness` | the Besov tightness criterion, reached through `prop:d4-diffusive-tightness` and `lem:sobolev-tightness`, which the paper cites at `sandpile.tex:1676-1680`; part (ii)(c) is those two propositions by `sandpile.tex:302-304`. Added at version 2 |
| `thm-main-explosion-iii-c` | `External.LocalCLT`, `External.ContinuumBesovTightness` | the same two that `thm:dgt4-diffusive-membrane` carries; part (iii)(c) is that theorem by `sandpile.tex:307-308`. Added at version 2 |
| `thm-main-explosion-iii-d` | `External.LocalCLT`, `External.ContinuumBesovTightness` | the local central limit theorem that `thm:dgt4-many-limits` carries, and the Besov criterion through `lem:sobolev-tightness` for the tightness clause; part (iii)(d) is that theorem by `sandpile.tex:308-309`. Added at version 2 |
| `thm-main-nontriviality` | `External.BallGreenBounds` | `eq:d4ball-time-tail`, reached through `thm:main-critical-level-percolation`, from which Theorem 1.1 is deduced at `sandpile.tex:317-342`. Added at version 3 |
| `thm-critical-toppling` | `External.VarianceScale`, `External.MultivariateBerryEsseen` | `eq:Qt-table`, `eq:corr-bound`; the multivariate Berry-Esseen comparison of `sandpile.tex:1770-1782` |
| `thm-critical-toppling-d4` | `External.VarianceScale` | `eq:Qt-table`, `eq:d4-full-window-bounds` |
| `prop-continuum-value-selfsimilar` | `External.VarianceScale` | `eq:Qt-table` |
| `prop-continuum-value-selfsimilar` | `External.LocalCLT` | Lawler–Limic Theorem 2.1.3, Eq. (2.8), cited at `sandpile.tex:1145-1161`, through the parabolic scaling limit `thm:main-explosion`(i)(b). |
| `prop-continuum-value-selfsimilar` | `External.ContinuumStoppingStability` | Coquet–Toldo Theorem 3 and Corollary 4, through the parabolic scaling limit `thm:main-explosion`(i)(b), used at `sandpile.tex:1995-1997`. The input is taken at the Brownian realization space’s universe, and the motion carries continuous paths and strongly measurable evaluations. The three conclusions are unchanged. |
| `prop-d4-pointwise-linearization` | `External.VarianceScale` | `eq:d4-window-l2`, `eq:d4-window-linfty` |
| `lem-d4-difference-tail` | `External.VarianceScale` | `eq:d4-full-window-bounds` |
| `cor-critical-mean-one` | `External.VarianceScale`, `External.MultivariateBerryEsseen` | `eq:Qt-table`, `eq:corr-bound`; the multivariate Berry-Esseen comparison of `sandpile.tex:1770-1782` |
| `prop-d4-one-point-gaussian` | `External.VarianceScale`, `External.PairedLocalCLTFour` | `eq:d4-window-l2`, `eq:d4-window-linfty`; Lawler–Limic Theorem 2.1.3 cited at `sandpile.tex:3250-3256` |
| `thm-main-explosion-ii-b` | `External.PairedLocalCLTFour` | Lawler–Limic Theorem 2.1.3 through `prop:d4-one-point-gaussian`, `sandpile.tex:3250-3256` |
| `prop-d4-superdiffusive-limit` | `External.VarianceScale` as well | `eq:d4-full-window-bounds`, `eq:d4-window-l2`, `eq:d4-window-linfty` |
| `prop-d4-superdiffusive-limit` | `External.MembraneScalingLimitFour` as well | Step 1, `sandpile.tex:3341-3342`, citing Cipriani-Hazra-Ruszel Theorem 2 and Cipriani-Dan-Hazra Theorem 3.11 for the convergence of the discrete membrane field; the truncation hypothesis it carries is the paper's own new point and is proved here |
| `thm-main-explosion-ii-c` | `External.MembraneScalingLimitFour` | the same citation through `prop:d4-superdiffusive-limit` |
| `thm-d4-critical-level-percolation` | `External.VarianceScale` as well | `eq:Qt-table`, `eq:d4-full-window-bounds` |
| `lem-dgt4-stretched-green-scenery-tail` | `External.GreenBoundsHigh` | `eq:dgt4-green-tail`, `eq:dgt4-green-l2` |
| `prop-dgt4-height-lower-stretched` | `External.GreenBoundsHigh` | `eq:dgt4-green-tail`, `eq:dgt4-green-l2` |
| `thm-dgt4-height-upper-tail` | `External.GreenBoundsHigh` | `eq:dgt4-tail-kernel` |
| `thm-main-explosion-iii-a` | `External.GreenBoundsHigh` | `eq:dgt4-green-tail`, `eq:dgt4-green-l2`, through `thm:dgt4-height-lower` |
| `thm-main-explosion-iii-b` | `External.GreenBoundsHigh` | `eq:dgt4-green-tail`, `eq:dgt4-green-l2`, `eq:dgt4-tail-kernel`, through `prop:dgt4-height-lower-stretched` and `thm:dgt4-height-upper-tail` |
| `lem-dgt4-level-shift-decoupling` | `External.GreenBoundsHigh` | `eq:dgt4-green-tail` |
| `lem-dgt4-cascade` | `External.GreenBoundsHigh` | `eq:dgt4-green-tail` |
| `thm-dgt4-nontriviality` | `External.GreenBoundsHigh`, `External.ExteriorBoundaryConnected` | `eq:dgt4-green-tail`; Timár Theorem 3 through `lem:dgt4-blocking-to-crossing`, `sandpile.tex:6595` |
| `thm-dgt4-many-limits` | `External.GreenBoundsHigh`, `External.LocalCLT` | `eq:dgt4-green-tail`, `eq:dgt4-green-l2`, `eq:dgt4-tail-kernel`, `eq:dgt4-intersection-first-moment`, `eq:dgt4-intersection-second-moment`, `eq:lclt-parity` |
| `thm-main-critical-level-percolation` | `External.BallGreenBounds`, `External.GreenBoundsHigh`, `External.VarianceScale` | `eq:d4ball-point`, `eq:d4ball-square`, `eq:d4ball-near`, `eq:d4ball-far-cube`, `eq:d4ball-shift`, `eq:d4ball-time-tail`, `eq:dgt4-green-tail`, `eq:Qt-table`, `eq:d4-full-window-bounds` |
| `prop-brownian-os` | `External.ContinuumOptimalStopping` | the finite-horizon optimal-stopping theorem applied to the gain `-h(T-s,B_s)`, Peskir and Shiryaev Theorem 2.2, cited at `sandpile.tex:1099` |
| `lem-sobolev-tightness` | `External.ContinuumBesovTightness` | the tightness criterion of Furlan and Mourrat, Theorem 2.30, at `p = q = 2` with regularity exponent `-β/2` and `α = -s`, together with the identification of `B^{-s,loc}_{2,2}` with `H^{-s}_loc`, cited at `sandpile.tex:1661-1662` and `sandpile.tex:1676-1680` |
| `prop-d4-diffusive-tightness` | `External.ContinuumBesovTightness` as well | the same criterion, reached through `lem:sobolev-tightness`, which the proof at `sandpile.tex:3288-3316` applies with `β = 2ε` |
| `cor-dlt4-mean-asymptotic` | `External.LocalCLT` | Lawler–Limic Theorem 2.1.3, Eq. (2.8), cited at `sandpile.tex:1145-1161`, through the parabolic scaling limit `thm:main-explosion`(i)(b). |
| `cor-dlt4-mean-asymptotic` | `External.ContinuumStoppingStability` | reached through `thm:main-explosion`(i)(b), which the corollary's proof applies at `T = 1` and at the origin (`sandpile.tex:2030-2032`). Added at version 4, taken at the universe of the corollary's own Brownian realization space and beside the path regularity of the motion at version 5 |
| `cor-dlt4-mean-asymptotic` | `External.VarianceScale` | reached through `prop:continuum-value-selfsimilar` (`sandpile.tex:1961-1980`), whose uniform exponential moment is the input the corollary's sentence names at `sandpile.tex:2030-2032`. Added at version 4 |
| `cor-dlt4-mean-asymptotic` | `External.ContinuumOptimalStopping` | Peskir and Shiryaev Theorem 2.2, cited at `sandpile.tex:1099`, reached through `prop:continuum-value-selfsimilar`; carried at the corollary's own Brownian realization space, exactly as that proposition carries it. Added at version 4 |
| `thm-main-explosion-i-b` | `External.LocalCLT` | Lawler–Limic Theorem 2.1.3, Eq. (2.8), cited at `sandpile.tex:1145-1161`, through the heat-potential invariance proposition used in the scaling proof at `sandpile.tex:1877-1879`. |
| `thm-main-explosion-i-b` | `External.ContinuumStoppingStability` | the stability of optimal-stopping values under uniform convergence of bounded rewards, together with the invariance principle for the stopped walk, Coquet and Toldo Theorem 3 and Corollary 4, cited at `sandpile.tex:1900-1907` and announced at `sandpile.tex:649`. Taken at the universe of the statement's own Brownian realization space, and the motion carries the path regularity of `lem:brownian-ball-localization`, at version 7 |
| `rem-dlt4-killed-scaling` | `External.ContinuumStoppingStability`, `External.CubeStoppingStability`, `External.LocalCLT` | Coquet–Toldo stopping stability and its killed form, `sandpile.tex:1900-1907` and `sandpile.tex:1929-1931`; the parity local central limit theorem `eq:lclt-parity` through `prop:dlt4-heat-potential-invariance`. The stopping stability is taken at the universe of the statement's two realization spaces at version 4 |

`thm-critical-toppling` and the corollary that follows it are the first two
nodes whose paper proof cites a work directly rather than through a display of
`ssec:green-estimates`.  The cited work is Raic's multivariate Berry-Esseen
theorem, and `Sandpile/External/BerryEsseen.lean` states it in the form the
proof applies, namely after the standardization by `\Sigma^{-1/2}` that the
paper performs: the comparison is between the law of the linear forms
`Y_j = \sum_i a_i(j)\xi_i` of an i.i.d. field and the centred Gaussian with the
covariance of those forms, on an orthant, with a constant depending on the third
moment ratio and on the conditioning of the covariance matrix.  The index set is
the finite set of coordinates the application reads, as in
`lem:weighted-exp-conc`; the paper's sum over `\Z^d` is finitely supported
because `g_{n_j}(0,\cdot)` is.

The matrix that `Sandpile.External.MultivariateBerryEsseen` feeds to
`multivariateGaussian` is never an arbitrary matrix: it is
`Sandpile.External.BerryEsseen.gram ν a`, which is `Var(ν)` times the Gram
matrix of the coefficient family, hence symmetric with a quadratic form that is
a nonnegative multiple of a sum of squares.  That is
`Sandpile.External.BerryEsseen.gram_posSemidef`, proved in
`Sandpile/Support/Gram.lean`, and it is why the statement needs no
positive-semidefiniteness hypothesis of its own: a comparison of Gaussian laws
that is false for a non-symmetric matrix is never invoked at one.

The last twelve rows were added after the citation graph of the paper was
extracted and closed transitively: every `\ref` inside every `\begin{proof}`,
iterated until the chain either terminates or reaches a display of
`ssec:green-estimates`.  Three of the twelve also reach `eq:rw-gaussian-upper`
or `eq:rw-max-displacement`, and they do not carry `External.HeatKernelBounds`
for that reason, because those two clauses are theorems here
(`Sandpile.External.gaussianUpper`, `Sandpile.External.maxDisplacement`) and a
proof reaching them assumes nothing.  `lem-dgt4-stretched-green-scenery-tail`
cites `\sum_y G(0,y)^2<\infty` and `G(0,y)\leq C(1+|y|)^{2-d}` in prose rather
than by `\ref`, so the extraction does not see it; the two are
`eq:dgt4-green-l2` and `eq:dgt4-green-tail`, and it carries them.

The quantitative paired local limit input `External.PairedLocalCLTFour`
records the summable remainder used in `sandpile.tex:1171-1172`. It is the
dimension-four specialization of Lawler–Limic Theorem 2.1.3, Eq. (2.8):
`p_n + p_{n+1}` differs from twice the Gaussian density by at most `C/n³`,
uniformly in the sites. The qualitative `External.LocalCLT` limit does not
state that remainder. The elementary paired-sum and logarithmic comparisons
are proved in `Support/DoubleSum.lean` and `Support/ExponentialHarmonic.lean`.

## Where a constant is bound, and why

The paper's constants "depend only on `d`", and in a formal statement that is a
property of quantifier order: a witness bound after a quantity may depend on it.
`tools/check_constants.py` reads every frozen statement for the pattern and is
one of the gates.

One statement was repaired.  `prop:continuum-value-selfsimilar` reads "For every
$T>0$ and every $x\in\R^d$, [the self-similarity].  There is $\theta>0$ such
that [the exponential moments].  In particular, for every $p>0$, [the moment
identity]" (`sandpile.tex:1961-1980`).  The middle sentence stands outside the
scope of `T` and `x`: it speaks only of `𝒰(1,0)` and of `𝒰_R(1,0)`, and `θ` is a
constant of the scenery law alone.  The frozen statement bound `T` and `x` as
theorem parameters, so its `∃ θ` sat inside their scope.  `T` and `x` are now
quantified inside the first and third conjuncts, where the paper has them, and
the `∃ θ` conjunct stands between them with no `T` and no `x` in scope
(`prop-continuum-value-selfsimilar`, version 3).

Five statements were read against the paper and are correct as they stand; the
reasons are recorded in the checker's own table, since that is where a reader
meets the question.

| node | the quantity | why the constant may depend on it |
|---|---|---|
| `prop-brownian-os` | `x` | the proposition opens "Fix $T>0$ and $x\in\R^d$"; the existentials are a right-continuous modification of the value process and the first time the value vanishes, both built from the path started at `x`, not constants |
| `thm-limiting-odometer-crossing` | `ε` | "For every $\varepsilon>0$, there are $T<\infty$ and $H>0$": the horizon and the height are chosen after the error, and a horizon uniform in the error would be false |
| `lem-finite-scale-extraction` | `ε` | "For every $\varepsilon>0$, there are $c>0$ and rational scales $s_1,\ldots,s_k$": the level and the list of scales are chosen after the error |
| `thm-main-explosion-ii-c` | `s` | "For every $T>0$ and $s>0$, the fields ... are tight in $H^{-s}_{\rm loc}$": the Sobolev exponent is fixed first, and the existential is the tightness threshold, which is per-exponent and per-error by definition |
| `prop-d4-superdiffusive-limit` | `s` | "Then, for every $s>0$": same reading, with the same tightness threshold |

A sixth report, on `lem-dgt4-path-survival`, was an artefact of the checker: it
read the type ascription `(m : ℝ)` inside the body of a hypothesis as a binder.
Only a top-level bracket group is a binder, and the checker now says so.

## Where the stopping value is read as a functional of the field

`prop:continuum-value-selfsimilar` opens "For every $T>0$ and every $x\in\R^d$,
$\mathcal U(T,x)\stackrel d= T^{(4-d)/4}\mathcal U(1,0)$"
(`sandpile.tex:1962-1966`).  Version 3 of the frozen statement asserted that
identity for `continuumValue` itself, with almost-everywhere measurability of
the two sides adjoined so that `Measure.map` would not take its junk value.
Version 4 asserts it instead for a measurable version `U` of the value: `U T x`
is measurable and agrees with `continuumValue … T x` almost everywhere, and the
identity of laws is the identity for `U`.

The reason is the paper's own proof.  `continuumValue` is an `sSup` over the
Brownian stopping times of `B x`, one family per starting point, and the proof
at `sandpile.tex:1988-1992` rescales time by `T`, which carries the stopping
times bounded by `T` of the motion started at `x` to the stopping times bounded
by one of `s ↦ T^{-1/2}(B_x(Ts)-x)`.  That rescaled motion is a Brownian motion
started at the origin but is not the member `B 0` of the given family, and
version 3 related the two sides' stopping families in no way at all.  What
licenses the descent from the equality in law of the two FIELDS, which is what
white-noise stationarity and Brownian scaling give, to the equality in law of
the two VALUES is that the stopping value is a measurable functional of the
field alone.  That is what `prop:brownian-os` supplies, on the one probability
space the theorem fixes: a measurable, right-continuous value process, with the
optimal time the first entry into the contact set the field determines.  A
measurable version is strictly more than version 3's almost-everywhere
measurability, so the repair weakens nothing the paper asserts.  The other two
conjuncts are unchanged (`prop-continuum-value-selfsimilar`, version 4;
authorized by the human on 2026-09-11).

## Cited inputs that are no longer cited

A cited result whose statement this repository can prove keeps its `Prop`, so
that no frozen statement changes, and gains a theorem beside it.

| the `Prop` and clause | the theorem that proves it |
|---|---|
| `External.OptimalStopping` | `Sandpile.External.optimalStopping` |
| `External.HeatKernelBounds`, first clause, the Gaussian upper bound | `Sandpile.External.gaussianUpper` |
| `External.HeatKernelBounds`, third clause, the maximal displacement | `Sandpile.External.maxDisplacement` |
| `External.VarianceScale`, all three clauses | `Sandpile.External.varianceScale` |
| `External.GreenBoundsHigh`, all five displays | `Sandpile.External.greenBoundsHigh` |
| the existence of white noise on `ℝ^d`, on which every `IsWhiteNoise` statement is quantified | `Sandpile.Continuum.exists_isWhiteNoise` |
| the existence of Brownian motion on `ℝ^d`, on which every `IsBrownian` statement is quantified | `Sandpile.Continuum.exists_isBrownian` |

Two identifications carry the last two.  The heat kernel `p_k(x, y)` depends on
its two arguments through their difference, and there it is the kernel of the
walk started at the origin, by the induction of
`Sandpile.External.heatKernel_eq_srwHeat`.  And the bounds proved for the walk
carry the `ℓ¹` norm of the displacement, whereas the paper writes the Euclidean
norm; since the Euclidean norm is at most the `ℓ¹` norm
(`Sandpile.External.latticeDist_le_graphNorm`), the event of the paper's
maximal-displacement bound is contained in the event of the proved one, and the
paper's Gaussian exponent is at most the proved one once `n + 2d ≤ (1 + 2d) n`
is used for `n ≥ 1`.

The second clause of `External.HeatKernelBounds`, the total-variation gradient
between two same-parity starts, is still assumed, as are `GreenBoundsHigh`,
`BallGreenBounds`, `LocalCLT` and `VarianceScale`.

Two identities that `External.VarianceScale` deliberately does not assume,
because they are the paper's own lines rather than the literature's, are now
theorems here as well: `Sandpile.variance_membrane` is
`Var(V_t(x)) = Var(ζ(0)) ∑_z g_t(x,z)^2` of `sandpile.tex:1179-1184`, and
`Sandpile.covariance_membrane` is
`Cov(V_m(x), V_n(y)) = Var(ζ(0)) ∑_z g_m(x,z) g_n(y,z)` of
`sandpile.tex:1197-1204`.  Both go through `Sandpile.measurePreserving_pick`,
which reads finitely many distinct sites of the field and carries its law to the
finite product of the one-site law; the variance of a linear functional is then
Mathlib's `variance_sum_pi` and the covariance is polarization.

## Frozen surface

<!-- FROZEN-SURFACE-BEGIN (generated by tools/sync_docs.py) -->

| id | Lean | paper | state |
|---|---|---|---|
| `thm-rw` | `Sandpile.Frozen.random_walk_representation` | `sandpile.tex:857-863`, `thm-RW` | SEALED |
| `ext-green-bounds-high` | `Sandpile.External.GreenBoundsHigh` | external input, Lawler-Limic Theorem 4.3.1 and Lawler Chapter 3, the d at least five estimates of ssec-green-estimates | FROZEN |
| `ext-ball-green-bounds` | `Sandpile.External.BallGreenBounds` | external input, Lawler-Limic Theorem 4.3.1 and Chapter 6, the ball-killed estimates of ssec-green-estimates | FROZEN |
| `ext-local-clt` | `Sandpile.External.LocalCLT` | external input, Lawler-Limic Theorem 2.1.3 Eq. (2.8), the local central limit theorem of ssec-green-estimates | FROZEN |
| `ext-variance-scale` | `Sandpile.External.VarianceScale` | external input, the finite-time variance scale, membrane correlations and window bounds of ssec-green-estimates | FROZEN |
| `lem-difference-representation` | `Sandpile.Frozen.difference_representation` | `sandpile.tex:928-936`, `lem-difference-representation` | SEALED |
| `lem-reflection-increment` | `Sandpile.Frozen.reflection_increment` | `sandpile.tex:899-905`, `lem-reflection-increment` | SEALED |
| `thm-optimal-stopping-proved` | `Sandpile.External.optimalStopping` | the cited optimal-stopping representation, proved from the shared library rather than assumed | SEALED |
| `ext-optimal-stopping` | `Sandpile.External.OptimalStopping` | external input, Theorem 3.2 of BPSH, the statement of thm-RW, now discharged by thm-optimal-stopping-proved | FROZEN |
| `lem-localization-killing` | `Sandpile.Frozen.localization_killing` | `sandpile.tex:1612-1617`, `lem-localization-killing` | SEALED |
| `thm-gaussian-upper-proved` | `Sandpile.External.gaussianUpper` | the cited Gaussian upper bound on the heat kernel, proved from the shared library rather than assumed | SEALED |
| `lem-weighted-exp-conc` | `Sandpile.Frozen.weighted_exp_concentration` | `sandpile.tex:1345-1405`, `lem-weighted-exp-conc` | SEALED |
| `lem-convex-linear-bound` | `Sandpile.Frozen.convex_linear_bound` | `sandpile.tex:1548-1570`, `lem-convex-linear-bound` | SEALED |
| `lem-dgt4-smoothed-odometer-tail` | `Sandpile.Frozen.dgt4_smoothed_odometer_tail` | `sandpile.tex:4461-4472`, `lem-dgt4-smoothed-odometer-tail` | SEALED |
| `ext-multivariate-berry-esseen` | `Sandpile.External.MultivariateBerryEsseen` | external input, Raic Theorem 1.1, the multivariate Berry-Esseen comparison used in the proof of thm-critical-toppling | FROZEN |
| `lem-dgt4-stretched-green-scenery-tail` | `Sandpile.Frozen.dgt4_green_scenery_tail` | `sandpile.tex:4385-4402`, `lem-dgt4-stretched-green-scenery-tail` | SEALED |
| `thm-white-noise-exists` | `Sandpile.Continuum.exists_isWhiteNoise` | the existence of white noise on R^d, proved from the shared library rather than assumed | SEALED |
| `thm-brownian-exists` | `Sandpile.Continuum.exists_isBrownian` | the existence of Brownian motion on R^d with generator Delta over 2d, proved from the shared library rather than assumed | SEALED |
| `prop-dgt4-height-lower-stretched` | `Sandpile.Frozen.dgt4_height_lower_stretched` | `sandpile.tex:4339-4350`, `prop-dgt4-height-lower-stretched` | SEALED |
| `cor-dgt4-mean-lower` | `Sandpile.Frozen.dgt4_mean_lower` | `sandpile.tex:4299-4314`, `cor-dgt4-mean-lower` | SEALED |
| `thm-variance-scale-proved` | `Sandpile.External.varianceScale` | the cited finite-time variance scale and window bounds, proved from the shared library rather than assumed | SEALED |
| `thm-dgt4-height-lower` | `Sandpile.Frozen.dgt4_height_lower` | `sandpile.tex:4168-4191`, `thm-dgt4-height-lower` | SEALED |
| `thm-dgt4-height-upper-tail` | `Sandpile.Frozen.dgt4_height_upper_tail` | `sandpile.tex:4501-4512`, `thm-dgt4-height-upper-tail` | SEALED |
| `thm-main-explosion-iii-a` | `Sandpile.Frozen.high_first_order` | `sandpile.tex:263-265`, `thm-main-explosion` | SEALED |
| `thm-main-explosion-iii-b` | `Sandpile.Frozen.high_tail` | `sandpile.tex:266-273`, `thm-main-explosion` | SEALED |
| `thm-green-bounds-high-proved` | `Sandpile.External.greenBoundsHigh` | the cited high-dimensional Green estimates, proved from the shared library rather than assumed | SEALED |
| `thm-critical-toppling` | `Sandpile.Frozen.critical_toppling` | `sandpile.tex:1703-1721`, `thm-critical-toppling` | SEALED |
| `cor-critical-mean-one` | `Sandpile.Frozen.critical_mean_one` | `sandpile.tex:1793-1799`, `cor-critical-mean-one` | SEALED |
| `lem-d4-difference-tail` | `Sandpile.Frozen.d4_difference_tail` | `sandpile.tex:3002-3015`, `lem-d4-difference-tail` | SEALED |
| `prop-d4-pointwise-linearization` | `Sandpile.Frozen.d4_pointwise_linearization` | `sandpile.tex:3060-3075`, `prop-d4-pointwise-linearization` | SEALED |
| `thm-critical-toppling-d4` | `Sandpile.Frozen.critical_toppling_d4` | `sandpile.tex:2692-2721`, `thm-critical-toppling-d4` | SEALED |
| `cor-d4-logarithmic-mean-lower` | `Sandpile.Frozen.d4_log_mean_lower` | `sandpile.tex:2971-2978`, `cor-d4-logarithmic-mean-lower` | SEALED |
| `lem-dgt4-origin-frozen` | `Sandpile.Frozen.dgt4_origin_frozen` | `sandpile.tex:4882-4918`, `lem-dgt4-origin-frozen` | SEALED |
| `lem-d4-finite-range-lower-bound` | `Sandpile.Frozen.d4_finite_range_lower_bound` | `sandpile.tex:3923-3931`, `lem-d4-finite-range-lower-bound` | SEALED |
| `lem-d4-exit-average-concentration` | `Sandpile.Frozen.d4_exit_average_concentration` | `sandpile.tex:3947-3958`, `lem-d4-exit-average-concentration` | SEALED |
| `thm-main-explosion-ii-a` | `Sandpile.Frozen.mean_growth_four` | `sandpile.tex:241-244`, `thm:main-explosion` | SEALED |
| `thm-main-explosion-ii-a-first-order` | `Sandpile.Frozen.four_first_order` | `sandpile.tex:245-246`, `thm:main-explosion` | SEALED |
| `ext-paired-local-clt-four` | `Sandpile.External.PairedLocalCLTFour` | sandpile.tex:1145-1172 (LawlerLimic Theorem 2.1.3 Eq. (2.8), paired dimension-four estimate) | FROZEN |
| `lem-d4-double-heat-kernel` | `Sandpile.Frozen.d4_double_heat_kernel` | `sandpile.tex:1164-1169`, `lem-d4-double-heat-kernel` | SEALED |
| `prop-d4-one-point-gaussian` | `Sandpile.Frozen.d4_one_point_gaussian` | `sandpile.tex:3243-3256`, `prop-d4-one-point-gaussian` | SEALED |
| `thm-main-explosion-ii-b` | `Sandpile.Frozen.four_gaussian` | `sandpile.tex:247-253`, `thm-main-explosion` | SEALED |
| `lem-d4-soft-bottleneck` | `Sandpile.Frozen.d4_soft_bottleneck` | `sandpile.tex:3451-3473`, `lem-d4-soft-bottleneck` | SEALED |
| `thm-heat-kernel-bounds-proved` | `Sandpile.External.heatKernelBounds` | `sandpile.tex:1126-1140`, `ssec-green-estimates` | SEALED |
| `lem-dgt4-localization` | `Sandpile.Frozen.dgt4_localization` | `sandpile.tex:6424-6435`, `lem-dgt4-localization` | SEALED |
| `lem-dgt4-level-shift-decoupling` | `Sandpile.Frozen.dgt4_level_shift_decoupling` | `sandpile.tex:6472-6486`, `lem-dgt4-level-shift-decoupling` | SEALED |
| `lem-dgt4-cascade` | `Sandpile.Frozen.dgt4_cascade` | `sandpile.tex:6543-6552`, `lem-dgt4-cascade` | SEALED |
| `ext-exterior-boundary-connected` | `Sandpile.External.ExteriorBoundaryConnected` | sandpile.tex:6600 (Timar Theorem 3, exterior nearest-neighbor boundary connectivity) | FROZEN |
| `lem-dgt4-blocking-to-crossing` | `Sandpile.Frozen.dgt4_blocking_to_crossing` | `sandpile.tex:6635-6642`, `lem-dgt4-blocking-to-crossing` | SEALED |
| `thm-dgt4-nontriviality` | `Sandpile.Frozen.dgt4_nontriviality` | `sandpile.tex:6672-6694`, `thm-dgt4-nontriviality` | SEALED |
| `ext-planar-rsw` | `Sandpile.External.PlanarRSW` | sandpile.tex:2235-2237 (Kohler-Schindler–Tassion Theorem 1 and Comment 1, planar crossing comparison) | FROZEN |
| `thm-d4-ball-green-crossing` | `Sandpile.Frozen.d4_ball_green_crossing` | `sandpile.tex:3548-3569`, `thm:d4-ball-green-crossing` | SEALED |
| `ext-lss-domination` | `Sandpile.External.LSSDomination` | sandpile.tex:2589,3992 (LSS Corollary 1.4) | FROZEN |
| `ext-continuum-optimal-stopping` | `Sandpile.External.ContinuumOptimalStopping` | sandpile.tex:1099 (PeskirShiryaev Theorem 2.2, finite-horizon optimal stopping for Brownian motion) | FROZEN |
| `prop-brownian-os` | `Sandpile.Frozen.brownian_optimal_stopping` | `sandpile.tex:1083-1099`, `prop-brownian-os` | SEALED |
| `lem-sobolev-tightness` | `Sandpile.Frozen.sobolev_tightness` | `sandpile.tex:1665-1675`, `lem-sobolev-tightness` | SEALED |
| `prop-d4-diffusive-tightness` | `Sandpile.Frozen.d4_diffusive_tightness` | `sandpile.tex:3290-3297`, `prop-d4-diffusive-tightness` | SEALED |
| `prop-weighted-membrane-limit` | `Sandpile.Frozen.weighted_membrane_limit` | `sandpile.tex:4736-4747`, `prop-weighted-membrane-limit` | SEALED |
| `lem-dgt4-weighted-last-visits` | `Sandpile.Frozen.dgt4_last_visits` | `sandpile.tex:4804-4820`, `lem-dgt4-weighted-last-visits` | SEALED |
| `ext-normal-comparison` | `Sandpile.External.NormalComparison` | sandpile.tex:5509-5516 (LiShao Corollary 2.1 p. 496, normal comparison inequality) | FROZEN |
| `ext-intersection-second-moment` | `Sandpile.External.IntersectionSecondMoment` | `sandpile.tex:1319-1324`, `eq-dgt4-intersection-second-moment` | FROZEN |
| `lem-dgt4-path-survival` | `Sandpile.Frozen.dgt4_path_survival` | `sandpile.tex:5513-5530`, `lem-dgt4-path-survival` | SEALED |
| `ext-continuum-rsw` | `Sandpile.External.ContinuumRSW` | sandpile.tex:2218 (KST Theorem 1 and Comment 1, continuum form on a field over a probability space) | FROZEN |
| `ext-pitt-gaussian-fkg` | `Sandpile.External.PittGaussianFKG` | sandpile.tex:2104 (Pitt Theorem p. 496 Eq. (1), Gaussian FKG) | FROZEN |
| `ext-gaussian-law-covariance` | `Sandpile.External.GaussianLawDeterminedByCovariance` | sandpile.tex:2110-2111 (the unit-scale field's invariances, which this classical fact supports, namely that a centred Gaussian field is determined in law by its covariance) | FROZEN |
| `ext-pinsker` | `Sandpile.External.Pinsker` | sandpile.tex:2390 (Pinsker inequality, total variation against relative entropy) | FROZEN |
| `thm-gaussian-law-covariance-proved` | `Sandpile.External.gaussianLawDeterminedByCovariance` | the determination of a centred Gaussian law by its covariance, proved from the shared library rather than assumed | SEALED |
| `thm-pinsker-proved` | `Sandpile.External.pinsker` | Pinsker's inequality on one measurable set, proved from the shared library rather than assumed | SEALED |
| `thm-d4-critical-level-percolation` | `Sandpile.Frozen.d4_critical_level_percolation` | `sandpile.tex:3996-4012`, `thm:d4-critical-level-percolation` | SEALED |
| `prop-dlt4-heat-potential-invariance` | `Sandpile.Frozen.heat_potential_invariance` | `sandpile.tex:1842-1849`, `prop-dlt4-heat-potential-invariance` | SEALED |
| `ext-cube-stopping-stability` | `Sandpile.External.CubeStoppingStability` | sandpile.tex:1929-1931 and sandpile.tex:1900-1907 (CoquetToldo Theorem 3 and Corollary 4, stability of killed optimal-stopping values) | FROZEN |
| `ext-gaussian-lipschitz-concentration` | `Sandpile.External.GaussianLipschitzConcentration` | sandpile.tex:5273-5278 (Borell 1975 and Tsirelson-Ibragimov-Sudakov 1976, Gaussian concentration for a Lipschitz functional) | FROZEN |
| `prop-dgt4-contact-asymptotics` | `Sandpile.Frozen.dgt4_contact_asymptotics` | `sandpile.tex:4867-4869`, `prop-dgt4-contact-asymptotics` | SEALED |
| `prop-dgt4-linearization` | `Sandpile.Frozen.dgt4_linearization` | `sandpile.tex:4782-4798`, `prop-dgt4-linearization` | SEALED |
| `thm-dgt4-diffusive-membrane` | `Sandpile.Frozen.dgt4_diffusive_membrane` | `sandpile.tex:4660-4683`, `thm-dgt4-diffusive-membrane` | SEALED |
| `thm-main-explosion-iii-c` | `Sandpile.Frozen.high_sobolev_limit` | `sandpile.tex:274-285`, `thm-main-explosion` | SEALED |
| `ext-membrane-scaling-four` | `Sandpile.External.MembraneScalingLimitFour` | external input, Cipriani-Hazra-Ruszel Theorem 2 and Cipriani-Dan-Hazra Theorem 3.11, the scaling limit of the four-dimensional discrete membrane field cited in Step 1 of prop-d4-superdiffusive-limit | FROZEN |
| `prop-d4-superdiffusive-limit` | `Sandpile.Frozen.d4_superdiffusive_limit` | `sandpile.tex:3329-3337`, `prop-d4-superdiffusive-limit` | SEALED |
| `thm-main-explosion-ii-c` | `Sandpile.Frozen.four_sobolev` | `sandpile.tex:254-258`, `thm-main-explosion` | SEALED |
| `ext-continuum-stopping-stability` | `Sandpile.External.ContinuumStoppingStability` | sandpile.tex:1900-1907 (CoquetToldo Theorem 3 and Corollary 4, stability of optimal-stopping values) | FROZEN |
| `ext-brownian-exit-step` | `Sandpile.External.BrownianExitStep` | sandpile.tex:1618, 1640-1658 (strong Markov at the ball exit time) | FROZEN |
| `thm-main-explosion-i-a` | `Sandpile.Frozen.mean_growth_le_three` | `sandpile.tex:213-215`, `thm:main-explosion` | SEALED |
| `lem-brownian-ball-localization` | `Sandpile.Frozen.brownian_ball_localization` | `sandpile.tex:1648-1659`, `lem-brownian-ball-localization` | SEALED |
| `ext-rellich-kondrachov-negsobolev` | `Sandpile.External.RellichKondrachovNegSobolev` | sandpile.tex:5615-5660 (RellichKondrachov compact Sobolev embedding, cited implicitly in the H-s-loc clause of lem:dgt4-linearization-from-survival) | FROZEN |
| `lem-dgt4-linearization-from-survival` | `Sandpile.Frozen.dgt4_linearization_from_survival` | `sandpile.tex:5659-5704`, `lem-dgt4-linearization-from-survival` | SEALED |
| `ext-ball-occupation-density` | `Sandpile.External.BallOccupationDensity` | sandpile.tex:2074-2088 (the kernel of X_s, in the context of eq:dlt4-linear-gaussian-potential), sandpile.tex:2499-2503 (expected occupation density); Morters-Peres, Brownian Motion, Ch. 3, Green function of a ball, theorem number not verified | FROZEN |
| `prop-continuum-value-selfsimilar` | `Sandpile.Frozen.continuum_value_self_similar` | `sandpile.tex:1962-1981`, `prop-continuum-value-selfsimilar` | SEALED |
| `thm-main-explosion-i-b` | `Sandpile.Frozen.brownian_scaling_limit` | `sandpile.tex:216-236`, `thm-main-explosion` | SEALED |
| `cor-dlt4-mean-asymptotic` | `Sandpile.Frozen.dlt4_mean_asymptotic` | `sandpile.tex:2041-2059`, `cor-dlt4-mean-asymptotic` | SEALED |
| `thm-dgt4-many-limits` | `Sandpile.Frozen.dgt4_many_limits` | `sandpile.tex:5944-5972`, `thm-dgt4-many-limits` | SEALED |
| `thm-d23-critical-level-percolation` | `Sandpile.Frozen.d23_critical_level_percolation` | `sandpile.tex:2569-2584`, `thm-d23-critical-level-percolation` | SEALED |
| `thm-main-critical-level-percolation` | `Sandpile.Frozen.critical_level_percolation` | `sandpile.tex:113-126`, `thm-main-critical-level-percolation` | SEALED |
| `thm-main-nontriviality` | `Sandpile.Frozen.percolation_below_criticality` | `sandpile.tex:95-103`, `thm-main-nontriviality` | SEALED |
| `thm-main-explosion-iii-d` | `Sandpile.Frozen.high_nonconvergence` | `sandpile.tex:286-293`, `thm-main-explosion` | SEALED |
| `lem-recursion` | `Sandpile.Frozen.odometer_recursion` | `sandpile.tex:817-822`, `lem-recursion` | SEALED |
| `cor-mean-localization` | `Sandpile.Frozen.mean_localization` | `sandpile.tex:1624-1634`, `cor-mean-localization` | SEALED |
| `lem-odometer-derivative` | `Sandpile.Frozen.odometer_derivative` | `sandpile.tex:868-881`, `lem-odometer-derivative` | SEALED |
| `rem-dlt4-killed-scaling` | `Sandpile.Frozen.dlt4_killed_scaling` | `sandpile.tex:1930-1957`, `rem-dlt4-killed-scaling` | SEALED |
| `lem-finite-scale-extraction` | `Sandpile.Frozen.finite_scale_extraction` | `sandpile.tex:2424-2434`, `lem-finite-scale-extraction` | SEALED |
| `thm-limiting-odometer-crossing` | `Sandpile.Frozen.limiting_odometer_crossing` | sandpile.tex:2515-2530 (thm-limiting-odometer-crossing); the stopping value is evaluated at the continuous heat-potential modification fixed at sandpile.tex:1019-1021, required by the stopped-field comparison at sandpile.tex:2500-2513; ball-field continuity is retained for finite-scale extraction | SEALED |
| `prop-fixed-scale-crossings` | `Sandpile.Frozen.fixed_scale_crossings` | `sandpile.tex:2130-2137`, `prop-fixed-scale-crossings` | SEALED |
| `prop-finite-time-concentration-scale` | `Sandpile.Frozen.finite_time_concentration_scale` | `sandpile.tex:1462-1487`, `prop-finite-time-concentration-scale` | SEALED |
| `ext-heat-kernel-bounds` | `Sandpile.External.HeatKernelBounds` | external input, Lawler-Limic Propositions 2.4.1 and 2.4.4 with Hoeffding, the estimates of ssec-green-estimates | FROZEN |
| `thm-max-displacement-proved` | `Sandpile.External.maxDisplacement` | the cited maximal-displacement estimate, proved from the shared library rather than assumed | SEALED |
| `ext-continuum-besov-tightness` | `Sandpile.External.ContinuumBesovTightness` | sandpile.tex:1676-1680 (FurlanMourrat Theorem 2.30 at p=q=2, covariance form, with the Besov-Sobolev identification) | FROZEN |

<!-- FROZEN-SURFACE-END -->
