import Sandpile.Law
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# The normal comparison inequality, cited

`Sandpile.External.NormalComparison` transcribes the comparison inequality of Li and Shao
(*Probability Theory and Related Fields* 122, 2002, Corollary 2.1): for a centred Gaussian
vector with covariance `S`, common variance `v`, and nonnegative correlations
`ρ_{ij} = S i j / v`, the probability of an orthant differs from the product of its
one-dimensional marginal probabilities by at most
`C ∑_{i<j} ρ_{ij} exp(-(b_i²+b_j²)/(2v(1+ρ_{ij})))`.  It specializes the source's inequality to
the nonnegative-correlation case the proof of `lem:dgt4-path-survival` applies it to, and is
cited rather than proved.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

-- FROZEN-STATEMENT-BEGIN
/-- The normal comparison inequality of `sandpile.tex:5506-5511`
(Li and Shao, Corollary 2.1, p. 496): for a centred Gaussian vector with
covariance `S`, common variance `v` and nonnegative correlations, the
probability of an orthant differs from the product of the one-dimensional
probabilities by at most
`C ∑_{i<j} ρ_{ij} exp(-(b_i²+b_j²)/(2v(1+ρ_{ij})))`, where `ρ_{ij} = S i j / v`.
Assumed, not proved. -/
def Sandpile.External.NormalComparison : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (m : ℕ) (v : ℝ≥0), 0 < v →
      ∀ S : Matrix (Fin m) (Fin m) ℝ, S.PosSemidef →
        (∀ i, S i i = (v : ℝ)) → (∀ i j, 0 ≤ S i j) →
        ∀ b : Fin m → ℝ,
          |(multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) S
                  {y : EuclideanSpace ℝ (Fin m) | ∀ i, y i ≤ b i}).toReal -
              ∏ i, (gaussianReal 0 v (Set.Iic (b i))).toReal| ≤
            C * ∑ i : Fin m, ∑ j ∈ Finset.Ioi i,
              S i j / (v : ℝ) *
                Real.exp (-(b i ^ 2 + b j ^ 2) /
                  (2 * (v : ℝ) * (1 + S i j / (v : ℝ))))
-- FROZEN-STATEMENT-END
