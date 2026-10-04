# Route: discharge `Sandpile.External.MultivariateBerryEsseen` (Raič, multivariate Berry–Esseen)

Status: **not discharged; no bounded proof attempted.** This file records the precise proof route,
the existing infrastructure, and the exact missing lemmas. Do not treat the Prop as proved.

Work target if reachable: a new file `LatticeProb/Prob/MultivariateBerryEsseen.lean`, namespace
`LatticeProb`, statement `LatticeProb.multivariateBerryEsseen` (or a near-identical name, grep-verified
before wiring). The DSP side then discharges its `FROZEN` definition by a theorem term of that type.
Nothing in `~/lean/Divisible-Sandpile-Percolation` is touched here.

## Target (frozen)

The brief cites
`~/lean/Divisible-Sandpile-Percolation/Sandpile/External/MultivariateBerryEsseen.lean`; that path
does **not** exist. The frozen Prop lives at
`Sandpile/External/BerryEsseen.lean`, export `Sandpile.External.MultivariateBerryEsseen`
(manifest node `ext-multivariate-berry-esseen`, `state: FROZEN`; file sha256
`f59d1224a9429e5a44f2fde03707a6ac8057c0c7b662acc95d71171cbc4ac2b8`). Its vocabulary is defined in
the same file:

```
Sandpile.External.BerryEsseen.gram ν a       : Matrix (Fin m) (Fin m) ℝ := variance id ν * ∑ i, a i j * a i k
Sandpile.External.BerryEsseen.coeffNorm a i  : ℝ := √(∑ j, a i j ^ 2)
Sandpile.External.BerryEsseen.quadForm S v   : ℝ := ∑ j, ∑ k, S j k * v j * v k
```

The frozen Prop, stripped of namespaces:

```
∀ M δ : ℝ, 0 < M → 0 < δ → δ < 1 →
  ∃ C : ℝ, 0 < C ∧
    ∀ (N m : ℕ), 1 ≤ m →
      ∀ ν : Measure ℝ, IsProbabilityMeasure ν →
        ∫ z, z ∂ν = 0 → 0 < variance id ν →
        Integrable (fun z => |z| ^ 3) ν →
        ∫ z, |z| ^ 3 ∂ν ≤ M * variance id ν ^ ((3 : ℝ) / 2) →
        ∀ a : Fin N → Fin m → ℝ,
          (∀ v : Fin m → ℝ,
            (1 - δ) * ∑ j, v j ^ 2 ≤ quadForm (gram ν a) v ∧
              quadForm (gram ν a) v ≤ (1 + δ) * ∑ j, v j ^ 2) →
          ∀ h : Fin m → ℝ,
            |((Measure.pi fun _ : Fin N => ν) {ξ | ∀ j, ∑ i, a i j * ξ i ≤ h j}).toReal -
                (multivariateGaussian 0 (gram ν a) {y | ∀ j, y j ≤ h j}).toReal| ≤
              C * (m : ℝ) ^ ((1 : ℝ) / 4) * variance id ν ^ ((3 : ℝ) / 2) *
                ∑ i, coeffNorm a i ^ 3
```

This is Raič, *A multivariate Berry–Esseen theorem with explicit constants*, Bernoulli 25 (2019),
Theorem 1.1, in the standardized orthant form the sandpile proof applies. The `m^{1/4}` is the
dimension factor; it is **not** a 1D rate and it is what makes the multivariate assembly genuinely
research-level (see Ingredient C).

The two dependents that consume it:

* `Sandpile.Frozen.critical_toppling` (`Sandpile/Frozen/CriticalToppling.lean`) — takes
  `hBerryEsseen` and feeds it to `Sandpile.exists_critical_toppling_bound` with
  `M = Mmom`, `δ = persistDelta` (`Sandpile/Support/CriticalScaleBound.lean:92`), `m` scales,
coefficients `a = stdCoeff d ν s ns`.
* `Sandpile.Frozen.critical_mean_one` (`Sandpile/Frozen/CriticalMeanOne.lean`) — same dependence
  through `critical_toppling`.

Instantiation pattern actually used (`Sandpile/Support/CriticalScaleBound.lean:94`): the conclusion
is read componentwise, both inequalities of `abs_le.mp hcomp`, and the Gaussian side is bounded
separately by `gaussian_orthant_le_kappa` (which uses `multivariateGaussian_orthant_le`, already in
the library). So the library-side proof only has to produce the orthant-vs-Gaussian difference; it
does not need to know anything about sandpiles.

## Existing infrastructure

Mathlib:

* `ProbabilityTheory.multivariateGaussian μ S` (`.../Gaussian/Multivariate.lean:168`), the
  pushforward of `stdGaussian (EuclideanSpace ℝ ι)` along `x ↦ μ + toEuclideanCLM (CFC.sqrt S) x`.
* `ProbabilityTheory.variance` (`.../Moments/Variance.lean:64`), `variance_nonneg`.
* `MeasureTheory.charFun`, `charFun_apply_real`, `charFun_gaussianReal`
  (`.../Gaussian/Real.lean:485`), `charFun_stdGaussian`, `charFun_pi`,
  `ProbabilityMeasure.tendsto_iff_tendsto_charFun`.
* `MeasureTheory.taylorWithinEval_charFun_two_zero` (the only quantitative charFun input in tree).
* Density/smoothing tools: `gaussianPDFReal`, `gaussianReal`, `integral_eq_sub_of_hasDerivAt`,
  `intervalIntegral.integral_deriv_eq_sub`, `MeasureTheory.integral_integral_swap`.
* **None** of: an explicit-constant 1D Berry–Esseen, a smoothing inequality, a multivariate
  smoothing inequality, or a quantitative Cramér–Wold.

LatticeProb:

* `LatticeProb.CramerWold.charFun_map_inner`, `.tendstoInDistribution_of_forall_inner`,
  `.tendstoInDistribution_pi_of_forall_dot`,
  `.tendstoInDistribution_pi_atTop_of_forall_dot`,
  `.tendstoInDistribution_of_map_eq` (`LatticeProb/Prob/CramerWold.lean`) — **qualitative** only.
  `tendstoInDistribution_pi_of_forall_dot` is the exact combinatorial device the quantitative
  proof would refine.
* `LatticeProb.charFun_second_order`, `LatticeProb.charFun_gaussian_second_order`
  (`LatticeProb/Prob/WeightedCLT.lean:64,78`) — the charFun–Gaussian comparison is `o(t²)` at `0`,
  i.e. **no explicit constant and no global bound**. This is the seed of Ingredient A.
* `LatticeProb.vonBahrEsseen` (`LatticeProb/Prob/VonBahrEsseenSum.lean:331`) — a `p ≤ 2` moment
  tail bound `P(|Σ Y_i| ≥ t) ≤ 2 M_p/t^p`. It is **not** a Berry–Esseen comparison.
* `LatticeProb.fukNagaev_tail` (`LatticeProb/Prob/FukNagaev.lean:865`) — polynomial + exponential
  tail; again not a BE comparison.
* `LatticeProb.multivariateGaussian_orthant_le`, `orthant_map_stdGaussian_le`,
  `orthant_le_of_le_smul`, `euclidean_gaussDensity_orthant`, `gaussianReal_Iic_eq`
  (`LatticeProb/Prob/GaussOrthant.lean`, `LatticeProb/Prob/GaussDensity.lean`) — the Gaussian
  orthant side, already sufficient.
* `LatticeProb.map_withDensity_linearEquiv_apply`, `stdGaussian_euclidean_eq_withDensity`,
  `prod_gaussianPDFReal` — change of variables for densities.

The library therefore has every ingredient of the proof **except the quantitative analytic core**
(Ingredient A) and the multivariate assembly (Ingredient C).

## Route

Three strictly nested pieces.

### Ingredient A — explicit one-dimensional Berry–Esseen (bounded, feasible)

This is the classical Esseen theorem with the constant left existential. It is feasible and is the
right first independent target.

A1. `charFun_third_order_le`. For a centred probability measure `ν` on `ℝ` with finite third
absolute moment,
```
theorem charFun_third_order_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ z, z ∂ν = 0) (h3 : Integrable (fun z => |z| ^ 3) ν) :
    ∀ t : ℝ,
      ‖charFun ν t - (1 - (variance id ν : ℂ) * (t : ℂ) ^ 2 / 2)‖
        ≤ |t| ^ 3 * (∫ z, |z| ^ 3 ∂ν) / 6
```
Route: `MeasureTheory.contDiff_charFun` gives the third derivative, whose value is
`(-I)^3 * ∫ z, z^3 * exp(I t z) ∂ν`; Taylor with integral remainder
(`taylor_isLittleO_univ` is not enough — need `Convex.norm_image_sub_le_of_norm_deriv_le` or the
integral form `Convex.integral_bound_of_deriv_le`). Missing as a packaged lemma; ~100–200 lines of
Taylor/interval-integral bookkeeping. (`charFun_second_order` already does the `o(t²)` version.)

A2. `charFun_exp_sub_le` and `charFun_decay`. With `σ² = variance id ν`, `ρ = ∫ |z|^3 ∂ν`:
```
theorem charFun_exp_sub_le ... :
    ∀ t, ‖charFun ν t - Complex.exp (-(σ² : ℂ) * (t:ℂ)^2 / 2)‖
      ≤ ρ * |t|^3 * Real.exp (-(σ² * t^2) / 8)
theorem charFun_norm_le_exp ... :
    ∀ t, ‖charFun ν t‖ ≤ Real.exp (-(σ² * t^2)/2 + ρ * |t|^3)
```
Route: `‖charFun ν t‖ ≤ 1 - σ²t²/2 + ρ|t|³ ≤ exp(-σ²t²/2 + ρ|t|³)` via `Real.exp_add`
and `Real.add_one_le_exp`; and the difference against `exp` via A1 plus the mean-value inequality
`|e^z - (1+z)| ≤ |z|² e^{|z|}`. These are short once A1 exists.

A3. `esseens_smoothing`. The 1D Berry–Esseen smoothing inequality:
```
theorem esseens_smoothing (μ μ' : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (M : ℝ) (hM : ∀ x, (μ' (Set.Iic x)).toReal ... derivative bound ...)
    (T : ℝ) (hT : 0 < T) :
    ∀ x, |(μ (Set.Iic x)).toReal - (μ' (Set.Iic x)).toReal|
      ≤ (1 / Real.pi) * ∫ u in (-T)..T, ‖charFun μ u - charFun μ' u‖ / |u| + 24 * M / (Real.pi * T)
```
For the Gaussian `μ' = gaussianReal 0 v`, `M = 1 / √(2πv)`. Route: the standard
`F(x) - G(x) = (1/2π) ∫ ∫ ... ` convolution argument. Missing entirely; ~150–300 lines. This is
the only genuinely 1D piece that is not already seeded in tree.

A4. `berryEsseen_oneDim`. Assembly of A1–A3 with the usual split of the integral into
`|t| ≤ 1/ρ'` and `1/ρ' < |t| ≤ T`, and `T = σ³/ρ`:
```
theorem berryEsseen_oneDim :
  ∃ C : ℝ, 0 < C ∧
    ∀ {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω) [IsProbabilityMeasure P]
      (Y : ι → Ω → ℝ), iIndepFun Y P →
      (∀ i, Integrable (Y i) P) → (∀ i, ∫ ω, Y i ω ∂P = 0) →
      (∀ i, Integrable (fun ω => |Y i ω| ^ 3) P) →
      (∑ i, ∫ ω, |Y i ω| ^ 3 ∂P) ≠ 0 →
      ∀ x : ℝ,
        |(P {ω | ∑ i, Y i ω ≤ x}).toReal -
          (gaussianReal 0 (∑ i, variance (Y i) P) (Set.Iic x)).toReal|
        ≤ C * (∑ i, ∫ ω, |Y i ω| ^ 3 ∂P) / (∑ i, variance (Y i) P) ^ ((3 : ℝ) / 2)
```
This is strictly easier than the target and should be attempted first; it is independent of the
multivariate machinery and would be reusable.

### Ingredient B — quantitative Cramér–Wold (bounded once A4 and C exist)

B1. `tendstoInDistribution_pi_of_forall_dot` is qualitative. Its quantitative refinement is:
```
theorem sup_orthant_le_of_sup_projection ...
    -- a bound on sup over directions of |P(projection)-Gaussian| transfers to a bound on the
    -- orthant difference, with a factor from a covering net of the boundary
```
This is where the `m`-dependence is generated. It is not independent work: it is a corollary of
the multivariate smoothing inequality (C1). Listed here only to make the dependency explicit.

### Ingredient C — multivariate orthant smoothing / Raič induction (research-level; the blocker)

This is the piece with no bounded proof. The target class is orthants of `ℝ^m`, and the rate is
`m^{1/4}`. The two viable formulations are:

C1. **Sazonov-type multivariate smoothing inequality.** For probability measures `μ, μ'` on
`ℝ^m` whose covariance quadratic forms are between `1-δ` and `1+δ`,
```
theorem orthant_smoothing_inequality ... :
    sup_{h : Fin m → ℝ} |(μ {y | ∀ j, y j ≤ h j}).toReal
        - (μ' {y | ∀ j, y j ≤ h j}).toReal|
      ≤ C(δ, m) * ∫_{‖t‖ ≤ T} ‖charFun μ t - charFun μ' t‖ / (∏ ...) dt + tail(T)
```
The multivariate smoothing kernel for an orthant is not the standard `∏ sin(t_j)/t_j` (the
orthant is not a difference of boxes in a way that is integrable at infinity in dimension `> 1`),
so the correct kernel is a Gaussian-smoothed orthant indicator, and the tail is controlled by the
Gaussian orthant estimate already in `GaussOrthant.lean`. Getting the `m^{1/4}` factor means the
`C(δ, m)` is `m^{1/4}` times a polynomial in `δ`, which requires a careful balance of the
smoothing bandwidth against the `m` coordinates. **No reference formalization exists and Mathlib
has nothing.**

C2. **Raič induction on the dimension.** Prove the `m`-dimensional comparison from the
`(m-1)`-dimensional one by conditioning on the last coordinate, applying A4 to the conditional
law of `Y_m` given the first `m-1` coordinates, and controlling the error by the near-isotropy of
`Σ`. The `m^{1/4}` arises from accumulating a `(1 + c/j^{...})` factor over the induction and
optimizing. This is closer to the published proof, but needs conditional characteristic functions
of the joint law of `(Y_1,...,Y_m)` given a coordinate, i.e. disintegration of
`Measure.pi ν` along a linear form, which is not in tree.

C3. **Direct via the `m`-fold product structure.** Bound the orthant difference by summing the
one-coordinate errors of a telescoping replacement of the joint law by the Gaussian. Each term is
a 1D BE error of a conditional law (A4), and the sum has `m` terms; the `m^{1/4}` then comes from
the trade-off between the number of terms and the conditional-variance lower bound supplied by
the near-isotropy. Same missing disintegrals as C2.

Recommended: attempt C1 after A4. If C1 proves too expensive, C3 is the cheapest mathematically
but needs a disintegration lemma (`MeasureTheory.Measure.disintegrate`) that is absent from
Mathlib.

### Assembly

D1. `multivariateBerryEsseen` (the target). Instantiate `quadForm (gram ν a)` as the covariance,
use C1 to compare the product law of `ξ` with the Gaussian orthant, and bound the Gaussian error
by the explicit `m^{1/4} Var(ν)^{3/2} Σ_i coeffNorm a i^3`. The constants `C` and the reduction of
the `h`-indexed supremum to the pointwise bound are bookkeeping. `variance id ν > 0` supplies the
`λ_min` lower bound; `∫ |z|³ ≤ M Var^{3/2}` supplies the moment ratio.

## Exact new-name requirements (grep-verified before wiring)

The names below are **not** in tree and must be created (or their Mathlib analogues found):

* `LatticeProb.charFun_third_order_le` — A1.
* `LatticeProb.charFun_exp_sub_le`, `LatticeProb.charFun_norm_le_exp` — A2.
* `LatticeProb.esseens_smoothing` — A3.
* `LatticeProb.berryEsseen_oneDim` — A4.
* `LatticeProb.orthant_smoothing_inequality` (or `LatticeProb.multivariateBerryEsseen_orthant`)
  — C1.
* `LatticeProb.multivariateBerryEsseen` — D1.
* Vocabulary `LatticeProb.mvbeGram`, `LatticeProb.mvbeCoeffNorm`, `LatticeProb.mvbeQuadForm`
  (or reuse the Sandpile names by importing DSP, which the library must not do).

## Alternatives considered and why rejected

* **`vonBahrEsseen` / `fukNagaev_tail`:** these bound `P(|ΣY_i| ≥ t)` by moments of the summands;
  they give rate `t^{-3}` for `p = 3`, but von Bahr–Esseen is only stated for `p ≤ 2`, and neither
  is a comparison with the Gaussian CDF. Not usable for the `|P - N|` difference.
* **`charFun_second_order` alone:** gives the local CLT with no constant; converting `o(t²)` to a
  uniform CDF bound needs the smoothing inequality (A3) and the global charFun decay (A2), which
  are exactly the missing pieces.
* **`Pinsker` / total variation:** yields a `√(KL)` bound, which for the near-isotropic Gaussian is
  a `√(Σ ρ²)`-type quantity, not the pointwise orthant difference with the exponential tail
  factor, and is dimensionally too large.
* **`CramerWold` as-is:** qualitative convergence, no rate. It can only be used after the rate is
  known, and it does not itself supply the `m^{1/4}`.

## Bridge to the DSP external

Once `LatticeProb.multivariateBerryEsseen` exists, the DSP side discharges
`ext-multivariate-berry-esseen` by defining `Sandpile.External.MultivariateBerryEsseen` to the
specialised instance (or by a bridge lemma in `Sandpile/External/BerryEsseen.lean` translating
`Sandpile.External.BerryEsseen.gram/coeffNorm/quadForm` to the LatticeProb vocabulary). The two
dependents then need no change other than to drop the hypothesis `hBerryEsseen` from
`Sandpile.Frozen.critical_toppling` and `Sandpile.Frozen.critical_mean_one` (and the downstream
`Sandpile.Support.CriticalScaleBound`, `CriticalAssembly`, `CriticalMeanOne`). The instantiation
`a = stdCoeff d ν s ns`, `M = Mmom`, `δ = persistDelta` in
`Sandpile/Support/CriticalScaleBound.lean:92` fixes the required quantifier order: `M` and `δ`
first, `C` existentially next, then `N, m, ν, a, h` — which is exactly the frozen statement.

## Scope / risk

* **A1–A4 (1D Berry–Esseen):** bounded, ~400–800 lines total. A3 (smoothing) is the only piece
  without a seed in tree; A1 is seeded by `charFun_second_order`.
* **C1 (multivariate smoothing with `m^{1/4}`):** research-level, no reference formalization. This
  is the reason the Prop is not discharged. Estimated 1000–3000 lines even with a concrete proof
  in hand, plus a disintegration/conditional-expectation layer absent from Mathlib.
* **D1:** small once C1 exists.

Recommendation: land A4 first as an independent library theorem (it is valuable on its own and
removes the largest single unknown), then decide whether C1 is in scope. Do **not** promote the
DSP `FROZEN` node unless C1 is actually formalized; until then the external remains a genuine
hypothesis, as the DSP `CORRESPONDENCE.md` already records.
