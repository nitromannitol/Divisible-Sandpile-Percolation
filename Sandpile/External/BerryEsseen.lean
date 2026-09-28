import Sandpile.Law
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# The multivariate Berry-Esseen theorem, standardized

`gram`, `coeffNorm` and `quadForm` set up the vocabulary for the multivariate Berry-Esseen
comparison of Raič (*Bernoulli* 25, 2019, Theorem 1.1): for i.i.d. mean-zero coordinates `ξ_i`
with coefficients `a`, `gram` is the covariance matrix `Σ` of the linear forms
`Y_j = ∑_i a_i(j) ξ_i`, `coeffNorm` is the Euclidean norm `|a(i)|` of the `i`-th coefficient
vector, and `quadForm` is the quadratic form in which the paper's spectral bound on `Σ` is
transcribed.  `Sandpile.External.MultivariateBerryEsseen` is the resulting comparison, cited
rather than proved, between the law of the standardized linear forms and the matching centred
Gaussian on the orthant `{y : y_j ≤ h_j}`; it is used by the proof of `thm:critical-toppling`.
-/

open MeasureTheory ProbabilityTheory

namespace Sandpile.External.BerryEsseen

/-- The covariance matrix `Σ` of the linear forms `Y_j = ∑_i a_i(j) ξ_i` when
the coordinates `ξ_i` are i.i.d. with one-site law `ν`:
`Σ_{jk} = \Var(ν)\sum_i a_i(j) a_i(k)`. -/
noncomputable def gram {N m : ℕ} (ν : Measure ℝ) (a : Fin N → Fin m → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun j k => variance id ν * ∑ i, a i j * a i k

/-- `|a(i)|`, the Euclidean norm of the coefficient vector of the `i`-th
coordinate. -/
noncomputable def coeffNorm {N m : ℕ} (a : Fin N → Fin m → ℝ) (i : Fin N) : ℝ :=
  Real.sqrt (∑ j, a i j ^ 2)

/-- The quadratic form `v ↦ ⟨Sv, v⟩` of a matrix, in which the paper's spectral
bound on `Σ` is transcribed. -/
noncomputable def quadForm {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ) (v : Fin m → ℝ) : ℝ :=
  ∑ j, ∑ k, S j k * v j * v k

end Sandpile.External.BerryEsseen

-- FROZEN-STATEMENT-BEGIN
/-- The multivariate Berry--Esseen comparison of `sandpile.tex:1770-1782`, in
the standardized form the proof of `thm:critical-toppling` applies: for an
i.i.d. mean-zero one-site law whose third absolute moment is at most `M` times
the `3/2` power of its variance, and coefficients `a` whose covariance matrix
`Σ` has quadratic form between `1-δ` and `1+δ`, the law of the linear forms
`Y_j = ∑_i a_i(j) ξ_i` and the centred Gaussian with covariance `Σ` assign
probabilities to the orthant `{y_j ≤ h_j}` differing by at most
`C m^{1/4} \Var(ν)^{3/2} ∑_i |a(i)|³`.  Assumed, not proved. -/
def Sandpile.External.MultivariateBerryEsseen : Prop :=
  ∀ M δ : ℝ, 0 < M → 0 < δ → δ < 1 →
    ∃ C : ℝ, 0 < C ∧
      ∀ (N m : ℕ), 1 ≤ m →
        ∀ ν : Measure ℝ, IsProbabilityMeasure ν →
          ∫ z, z ∂ν = 0 → 0 < variance id ν →
          Integrable (fun z => |z| ^ 3) ν →
          ∫ z, |z| ^ 3 ∂ν ≤ M * variance id ν ^ ((3 : ℝ) / 2) →
          ∀ a : Fin N → Fin m → ℝ,
            (∀ v : Fin m → ℝ,
              (1 - δ) * ∑ j, v j ^ 2 ≤
                  Sandpile.External.BerryEsseen.quadForm
                    (Sandpile.External.BerryEsseen.gram ν a) v ∧
                Sandpile.External.BerryEsseen.quadForm
                    (Sandpile.External.BerryEsseen.gram ν a) v ≤
                  (1 + δ) * ∑ j, v j ^ 2) →
            ∀ h : Fin m → ℝ,
              |((Measure.pi fun _ : Fin N => ν)
                      {ξ | ∀ j, ∑ i, a i j * ξ i ≤ h j}).toReal -
                  (multivariateGaussian 0
                      (Sandpile.External.BerryEsseen.gram ν a)
                      {y | ∀ j, y j ≤ h j}).toReal| ≤
                C * (m : ℝ) ^ ((1 : ℝ) / 4) * variance id ν ^ ((3 : ℝ) / 2) *
                  ∑ i, Sandpile.External.BerryEsseen.coeffNorm a i ^ 3
-- FROZEN-STATEMENT-END
