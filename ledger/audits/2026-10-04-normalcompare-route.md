# Route: discharge `Sandpile.External.NormalComparison` (Li–Shao orthant comparison)

Status: **not discharged; no bounded proof attempted.** This file records the precise proof route,
the existing infrastructure, and the exact missing lemmas. Do not treat the Prop as proved.

## Target

The frozen Prop (`~/lean/Divisible-Sandpile-Percolation/Sandpile/External/NormalComparison.lean`):

```
∃ C : ℝ, 0 < C ∧ ∀ m, ∀ v : ℝ≥0, 0 < v → ∀ S : Matrix (Fin m) (Fin m) ℝ, S.PosSemidef →
  (∀ i, S i i = v) → (∀ i j, 0 ≤ S i j) → ∀ b : Fin m → ℝ,
    |(multivariateGaussian 0 S {y | ∀ i, y i ≤ b i}).toReal
       - ∏ i, (gaussianReal 0 v (Iic (b i))).toReal|
    ≤ C * ∑ i, ∑ j ∈ Ioi i, S i j / v * exp (-(b i² + b j²) / (2 v (1 + S i j / v)))
```

Work target if reachable: `LatticeProb/Prob/NormalComparison.lean`, namespace `LatticeProb`,
statement `LatticeProb.normalComparison` (specialised to `Matrix (Fin m) (Fin m) ℝ` and
`EuclideanSpace ℝ (Fin m)`). The DSP side then discharges the `FROZEN` definition by replacing it
with a theorem term of that type (or by importing and re-exporting). The library-side name and
namespace must be grep-verified before wiring.

## Existing infrastructure

Mathlib (`Mathlib/Probability/Distributions/Gaussian/Multivariate.lean`, `Real.lean`):

* `ProbabilityTheory.multivariateGaussian μ S`, defined as
  `(stdGaussian (EuclideanSpace ℝ ι)).map (fun x => μ + toEuclideanCLM (CFC.sqrt S) x)`.
* `covariance_eval_multivariateGaussian`, `variance_eval_multivariateGaussian`.
* `measurePreserving_restrict₂_multivariateGaussian hS hJI`: pushing
  `multivariateGaussian μ S` forward along `EuclideanSpace.restrict₂ hJI` gives the marginal with
  the submatrix covariance. This is the bivariate-marginal tool (`J = {i,j}`).
* `gaussianPDFReal`, `gaussianReal`, `gaussianReal_of_var_ne_zero`,
  `integral_gaussianPDFReal_eq_one`, `gaussianPDFReal_pos`.
* `hasDerivAt_integral_of_dominated_loc_of_deriv_le`,
  `hasDerivAt_integral_of_dominated_loc_of_lip` (`Analysis/Calculus/ParametricIntegral.lean`).
* `Matrix.PosDef.isUnit`, `Matrix.det`, `Matrix.inv`, `CFC.sqrt`, `CFC.sqrt_mul_sqrt_self`.

LatticeProb:

* `LatticeProb.stdGaussian_euclidean_eq_withDensity` — the standard Gaussian on
  `EuclideanSpace ℝ ι` has the product density `∏ i, gaussianPDF 0 1 (y i)`.
* `LatticeProb.map_withDensity_linearEquiv_apply` — pushforward of a density along a linear
  equivalence (the change-of-variables tool for the covariance).
* `LatticeProb.map_withDensity_measurePreserving`.
* `LatticeProb.prod_gaussianPDFReal`, `LatticeProb.prod_gaussianPDF`.
* `LatticeProb.euclidean_gaussDensity_orthant` — orthant of a product Gaussian.
* `LatticeProb.orthant_le_of_le_smul` — orthant bound from a density comparison.
* `LatticeProb.gaussianReal_Iic_eq` — 1D marginal at variance `v` rescaled from variance `1`.

There is **no** density for `multivariateGaussian` with a general covariance, no
derivative-in-covariance lemma, and no integration-by-parts lemma for the orthant boundary. Those
are the missing pieces.

## Route: smart-path interpolation

Fix `m`, `v > 0`, `S` PSD with diagonal `v` and `S i j ≥ 0`, and `b`. Put `ρ i j := S i j / v`
(so `0 ≤ ρ i j ≤ 1`, `ρ i i = 1`). Define the path

```
Sfun t := (1 - t) • (v • 1) + t • S,        t ∈ [0,1]
F t    := (multivariateGaussian 0 (Sfun t) {y | ∀ i, y i ≤ b i}).toReal.
```

`Sfun 0 = v • 1` gives the product law, `Sfun 1 = S`; every `Sfun t` is PSD with diagonal `v` and
off-diagonal `t * S i j ≥ 0`. Then

```
|F 1 - F 0| = F 1 - F 0 = ∫_0^1 deriv F t dt
```

(Slepian monotonicity in the nonnegative correlations gives `deriv F t ≥ 0`, so the absolute value
can be dropped). The derivative is the boundary density integral

```
deriv F t = ∑ i ∑ j ∈ Ioi i, S i j * D i j t,
D i j t   = ∫_{y_{-ij} ≤ b_{-ij}} p_{Sfun t}(y with y i = b i, y j = b j) dy_{-ij},
```

obtained by differentiating the density in the covariance (`∂ p_Σ / ∂Σ_{ij} = ∂²_{ij} p_Σ` for the
free symmetric entry) and integrating by parts twice. Since `S i j ≥ 0` and `D i j t ≥ 0`, this is
manifestly nonnegative.

The estimate that closes: write the full density as
`p(x) = p_{ij}(x_i,x_j; correlation t ρ i j) · p_{-ij|ij}(x_{-ij} | x_i,x_j)`. Then

```
D i j t = p_{ij}(b i, b j; t ρ i j) · P(Y_{-ij} ≤ b_{-ij} | Y i = b i, Y j = b j)
        ≤ p_{ij}(b i, b j; t ρ i j).
```

The bivariate density is

```
p_{ij}(a,b; r) = 1 / (2 π v √(1 - r²)) · exp (-(a² - 2 r a b + b²) / (2 v (1 - r²))).
```

For `0 ≤ t ≤ 1`, `ρ ≥ 0`, the exponent comparison (AM–GM: `2 a b ≤ a² + b²`) gives

```
-(a² - 2 t ρ a b + b²) / (2 v (1 - (t ρ)²)) + 1/(...) ≤ exp (-(a² + b²) / (2 v (1 + ρ)))
```

up to the prefactor `(1/(2πv)) (1 - (tρ)²)^{-1/2}`; the identity
`(1 + ρ) - (1 - (tρ)²) = ρ + t²ρ²` and `t(1+ρ) ≤ 1 + t²ρ` for `0 ≤ t ≤ 1`, `0 ≤ ρ ≤ 1` verify it.
Finally `∫_0^1 (1 - (tρ)²)^{-1/2} dt = arcsin(ρ)/ρ ≤ π/2` (and `= 1` for `ρ = 0`), so

```
∫_0^1 D i j t dt ≤ (max 1 (π/2)) / (2 π v) · exp (-(b i² + b j²) / (2 v (1 + ρ i j))).
```

Summing and multiplying by `S i j = v ρ i j` gives the target with
`C = max 1 (π/2) / (2π)`, absorbing the finitely many terms; `C > 0` is immediate.

## Exact missing lemmas (dependency order)

Suggested locations in `LatticeProb/Prob/NormalComparison.lean` unless noted.

1. `multivariateGaussian_eq_withDensity` (the density of a nondegenerate multivariate Gaussian).
   For `S.PosDef`,
   `multivariateGaussian 0 S = volume.withDensity (fun x => ENNofReal ((2π)^(-m/2) * (det S)^(-1/2)
   * exp (-(x ⬝ᵥ S⁻¹ *ᵥ x) / 2)))` on `EuclideanSpace ℝ (Fin m)`.
   Route: `multivariateGaussian` is the pushforward of `stdGaussian` along
   `toEuclideanCLM (CFC.sqrt S)`, which is a linear equivalence when `S.PosDef`;
   rewrite `stdGaussian` with `stdGaussian_euclidean_eq_withDensity`, apply
   `map_withDensity_linearEquiv_apply`; compute `det (CFC.sqrt S) = √(det S)`,
   `(CFC.sqrt S).symm`, and `∏ gaussianPDF 0 1` in terms of `x ⬝ᵥ S⁻¹ *ᵥ x`.
   This is the single largest missing piece (~200–400 lines; the matrix-CFC algebra is the risk).
   A `PosSemidef` version is not needed if the path is handled by a limit (see item 8).

2. `posSemidef_smul_add_smul` and the path facts: `(Sfun t).PosSemidef`,
   `∀ i, Sfun t i i = v`, `∀ i j, 0 ≤ Sfun t i j`, `Sfun 0 = v • 1`, `Sfun 1 = S`, and continuity
   of `t ↦ Sfun t`. All are `Matrix.PosSemidef` convexity + `Matrix.ext` + arithmetic.

3. `hasDerivAt_orthant_multivariateGaussian`: for `S : ℝ → Matrix ...` with `HasDerivAt` and a
   uniform PosDef/`det` lower bound on a neighbourhood of `t`,
   `HasDerivAt (fun t => (multivariateGaussian 0 (S t) {y | ∀ i, y i ≤ b i}).toReal)
     (∑ i ∑ j ∈ Ioi i, deriv S t i j * boundaryIntegral (S t) b i j) t`.
   Route: integrate the pointwise `HasDerivAt` of `s ↦ p_{S s}(x)` against the orthant indicator,
   using `hasDerivAt_integral_of_dominated_loc_of_deriv_le` with the density/derivative bounds
   from item 1 and a uniform Gaussian majorant. Needs the chain rule for `Matrix.det`,
   `Matrix.inv`, and `CFC`-free `S⁻¹` on the PosDef neighbourhood.

4. `orthant_deriv_eq_boundaryIntegral` (integration by parts in two coordinates): for smooth
   rapidly-decaying `p` on `EuclideanSpace ℝ (Fin m)`,
   `∫_{y ≤ b} ∂²_{ij} p y dy = ∫_{y_{-ij} ≤ b_{-ij}} p (b i, b j, y_{-ij}) dy_{-ij}`.
   Route: Fubini (`MeasureTheory.integral_integral_swap`) + two uses of the 1D
   `intervalIntegral.integral_deriv_eq_sub` / `integral_eq_sub_of_hasDerivAt` on the inner
   coordinates. Missing in Mathlib for the general `m`-dimensional orthant.

5. `boundaryIntegral_le_bivariateDensity`:
   `boundaryIntegral (Sfun t) b i j ≤ bivariateGaussianPDFReal v (S i j * t / v) (b i) (b j)`,
   by factorising the density into the `{i,j}` marginal (item 1 + `measurePreserving_restrict₂_multivariateGaussian`
   on `J = {i,j}`) times a conditional density whose integral over `y_{-ij} ≤ b_{-ij}` is `≤ 1`.

6. `bivariateGaussianPDFReal_le`: the pointwise exponential/AM–GM bound
   `bivariateGaussianPDFReal v r a b ≤ (1 / (2 π v)) * (1 - r²)^(-1/2)
     * exp (-(a² + b²) / (2 v (1 + r)))` for `0 ≤ r ≤ 1`, using `2 a b ≤ a² + b²`,
   `(1 + r) - (1 - r²) = r + r²`, and `t (1 + r) ≤ 1 + t² r` at `r = t ρ`.

7. `integral_bivariateGaussianPDFReal_le`: `∫_0^1 (1 - (t r)²)^(-1/2) dt = arcsin r / r ≤ π/2`
   (and `= 1` at `r = 0`), via `Real.arcsin` and FTC; then the `t`-integral bound.

8. Assembly `normalComparison`: combine 3, 4, 5, 6, 7 with
   `intervalIntegral.integral_eq_sub_of_hasDerivAt` (or `HasDerivAt` + `integral_eq_sub_of_hasDerivAt`)
   over `[0,1]`; sum, use `S i j = v ρ i j`, and set `C = max 1 (π/2) / (2π)`.
   Handle `S.PosSemidef` (possibly singular): either (a) prove item 1 only for `PosDef` and
   approximate `S` by `S + ε • 1` with a renormalisation that preserves the diagonal (add
   `ε • 1` then rescale off-diagonals, which changes `ρ` to `ρ/(1+ε)`, and take `ε ↓ 0`), or
   (b) integrate over `range (CFC.sqrt S)` and use the co-area/marginal form directly. Case (a) is
   the lower-risk route but needs a continuity-of-orthant-probability-in-S lemma (missing; ~100
   lines with `MeasureTheory.tendsto_measure_of_tendsto_of_monotone`/portmanteau on the density).

## Alternatives considered and why rejected

* **Pinsker / total variation** (`LatticeProb.pinsker`, `abs_sub_le_tvDist`): gives
  `|P - ∏| ≤ √(2 KL)` with `KL = -(1/2) log det (diag(S)⁻¹ S) ≈ (1/4) ∑ ρ²`, i.e. a `√(∑ρ²)`-type
  bound. This is `≫` the target linear-in-`ρ` bound with the exponential tail factor; and it does
  not see `b`. Not usable.
* **`multivariateGaussian_orthant_le` / `orthant_le_of_le_smul`**: these compare an orthant to a
  product with a *different* variance under near-isotropy and lose the `∑_{i<j} ρ_{ij} exp(...)`
  term entirely. They give the `ρ = 0` case only.
* **Naive interpolation on the standard Gaussian with `A_t = CFC.sqrt (Sfun t)`**: differentiability
  of `CFC.sqrt` along `t` and the co-area formula are harder than items 1–4.

## Scope / risk

The mathematics is elementary (smart path + AM–GM + `∫ (1-(tρ)²)^{-1/2}`); the cost is formal:
items 1, 3 and 4 are the hard, novel pieces, and item 8(a) (singular `S`) is a likely source of
grind. Estimate ~1500–3000 lines. Recommended split into separate files
(`GaussMultivariateDensity.lean`, `OrthantInterpolation.lean`) with items 1 and 4 as independent
targets. The frozen Prop itself is untouched; this route only prepares the library proof that
would let the DSP `FROZEN` node be promoted.
