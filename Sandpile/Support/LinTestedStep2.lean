/-
Step 2 of `lem:dgt4-linearization-from-survival` (`sandpile.tex:5803-5845`) for
the tested field itself.

The abstract Step 2 of `Support/LinConvexStep2.lean` asks for a coordinatewise
convex functional reading finitely many sites, with right derivatives between
`0` and a coefficient whose squares are uniformly summable.  The tested field of
`Support/LinTestedField.lean` is one, with coefficient
`b_R(z) = ∑_x a_R(x) g_{n_R}(x,z)`, so the whole of Step 2 for `F_R` reduces to
the three estimates the paper proves in Step 1 and in
`eq:dgt4-tested-green-bound`.
-/
import Sandpile.Support.LinConvexStep2
import Sandpile.Support.LinTestedField
import Sandpile.Support.LinTestedJacobian

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile

variable {d : ℕ}

/-- The coefficient bound of `sandpile.tex:5786-5790`: `b_R(z) = ∑_x a_R(x) g_{n_R}(x,z)`. -/
noncomputable def testedGreenWeight (s : Finset (Site d)) (a : Site d → ℝ) (n : ℕ)
    (v : Site d) : ℝ :=
  ∑ x ∈ s, a x * greenTime d n x v

/-- **Step 2 of `lem:dgt4-linearization-from-survival` for the tested field.**
`eq:dgt4-convex-linear-remainder` and `eq:dgt4-linear-coefficient-replacement`
give `eq:dgt4-linearization-from-paths`, once Step 1 supplies the vanishing
derivative-variance sum and the mean-gradient approximation, and
`eq:dgt4-tested-green-bound` the uniform bound on the coefficients. -/
theorem tendsto_l2_testedField {l : Filter ℝ}
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ z, z ∂ν = 0) (hsq : Integrable (fun z => z ^ 2) ν)
    (s : ℝ → Finset (Site d)) (a : ℝ → Site d → ℝ) (n : ℝ → ℕ)
    (ha : ∀ (R : ℝ) (x : Site d), 0 ≤ a R x)
    (coef : ℝ → Site d → ℝ) (B₀ : ℝ)
    (hB₀ : ∀ R : ℝ,
      ∑ v ∈ testedSites (s R) (n R), testedGreenWeight (s R) (a R) (n R) v ^ 2 ≤ B₀)
    (hVar : Tendsto (fun R : ℝ => ∑ v ∈ testedSites (s R) (n R),
        variance (rightDerivField (testedField (s R) (a R) (n R)) v)
          (LatticeProb.iidLaw d ν)) l (𝓝 0))
    (hcoef : Tendsto (fun R : ℝ => ∑ v ∈ testedSites (s R) (n R),
        ((∫ η, rightDerivField (testedField (s R) (a R) (n R)) v η ∂(LatticeProb.iidLaw d ν))
          - coef R v) ^ 2) l (𝓝 0))
    (hI1 : ∀ R : ℝ, Integrable (fun ζ => (testedField (s R) (a R) (n R) ζ
        - (∫ η, testedField (s R) (a R) (n R) η ∂(LatticeProb.iidLaw d ν))
        - ∑ v ∈ testedSites (s R) (n R),
            (∫ η, rightDerivField (testedField (s R) (a R) (n R)) v η
              ∂(LatticeProb.iidLaw d ν)) * ζ v) ^ 2) (LatticeProb.iidLaw d ν))
    (hI2 : ∀ R : ℝ, Integrable (fun ζ =>
        (∑ v ∈ testedSites (s R) (n R),
            (∫ η, rightDerivField (testedField (s R) (a R) (n R)) v η
              ∂(LatticeProb.iidLaw d ν)) * ζ v
          - ∑ v ∈ testedSites (s R) (n R), coef R v * ζ v) ^ 2) (LatticeProb.iidLaw d ν))
    (hI3 : ∀ R : ℝ, Integrable (fun ζ => (testedField (s R) (a R) (n R) ζ
        - (∫ η, testedField (s R) (a R) (n R) η ∂(LatticeProb.iidLaw d ν))
        - ∑ v ∈ testedSites (s R) (n R), coef R v * ζ v) ^ 2) (LatticeProb.iidLaw d ν)) :
    Tendsto (fun R : ℝ => ∫ ζ, (testedField (s R) (a R) (n R) ζ
        - (∫ η, testedField (s R) (a R) (n R) η ∂(LatticeProb.iidLaw d ν))
        - ∑ v ∈ testedSites (s R) (n R), coef R v * ζ v) ^ 2
      ∂(LatticeProb.iidLaw d ν)) l (𝓝 0) :=
  tendsto_l2_linear_of_convex ν hmean hsq
    (fun R => testedSites (s R) (n R))
    (fun R => testedField (s R) (a R) (n R))
    (fun R v => rightDerivField (testedField (s R) (a R) (n R)) v)
    (fun R => testedGreenWeight (s R) (a R) (n R))
    coef
    (fun R => measurable_testedField (s R) (a R) (n R))
    (fun R ζ η h => testedField_congr (s R) (a R) (n R) ζ η fun z hz => h z hz)
    (fun R v => measurable_rightDerivField _ (measurable_testedField (s R) (a R) (n R)) v
      fun ζ => convexOn_testedField_update (s R) (a R) (n R) (fun x _ => ha R x) v ζ)
    (fun R v ζ => convexOn_testedField_update (s R) (a R) (n R) (fun x _ => ha R x) v ζ)
    (fun R v ζ => hasDerivWithinAt_rightDerivField _ v ζ
      (convexOn_testedField_update (s R) (a R) (n R) (fun x _ => ha R x) v ζ))
    (fun R => Filter.Eventually.of_forall fun ζ v _ =>
      ⟨rightDerivField_testedField_nonneg (s R) (a R) (n R) (fun x _ => ha R x) v ζ,
        rightDerivField_testedField_le (s R) (a R) (n R) (fun x _ => ha R x) v ζ⟩)
    B₀ hB₀ hVar hcoef hI1 hI2 hI3

/-- **Step 2 of `lem:dgt4-linearization-from-survival`, in the paper's own
vocabulary.**  The derivative variances and mean gradients are the ones of
`eq:odometer-derivative`, and the two remaining inputs are
`eq:dgt4-derivative-variance-limit` and
`eq:dgt4-mean-gradient-approximation`. -/
theorem tendsto_l2_testedField_jacobian {l : Filter ℝ}
    (ν : Measure ℝ) [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (hmean : ∫ z, z ∂ν = 0) (hsq : Integrable (fun z => z ^ 2) ν)
    (s : ℝ → Finset (Site d)) (a : ℝ → Site d → ℝ) (n : ℝ → ℕ)
    (ha : ∀ (R : ℝ) (x : Site d), 0 ≤ a R x)
    (coef : ℝ → Site d → ℝ) (B₀ : ℝ)
    (hB₀ : ∀ R : ℝ,
      ∑ v ∈ testedSites (s R) (n R), testedGreenWeight (s R) (a R) (n R) v ^ 2 ≤ B₀)
    (hVar : Tendsto (fun R : ℝ => ∑ v ∈ testedSites (s R) (n R),
        variance (fun ζ => ∑ x ∈ s R, a R x * odometerJacobian ζ (n R) x v)
          (LatticeProb.iidLaw d ν)) l (𝓝 0))
    (hcoef : Tendsto (fun R : ℝ => ∑ v ∈ testedSites (s R) (n R),
        ((∫ η, (∑ x ∈ s R, a R x * odometerJacobian η (n R) x v) ∂(LatticeProb.iidLaw d ν))
          - coef R v) ^ 2) l (𝓝 0))
    (hI1 : ∀ R : ℝ, Integrable (fun ζ => (testedField (s R) (a R) (n R) ζ
        - (∫ η, testedField (s R) (a R) (n R) η ∂(LatticeProb.iidLaw d ν))
        - ∑ v ∈ testedSites (s R) (n R),
            (∫ η, (∑ x ∈ s R, a R x * odometerJacobian η (n R) x v)
              ∂(LatticeProb.iidLaw d ν)) * ζ v) ^ 2) (LatticeProb.iidLaw d ν))
    (hI2 : ∀ R : ℝ, Integrable (fun ζ =>
        (∑ v ∈ testedSites (s R) (n R),
            (∫ η, (∑ x ∈ s R, a R x * odometerJacobian η (n R) x v)
              ∂(LatticeProb.iidLaw d ν)) * ζ v
          - ∑ v ∈ testedSites (s R) (n R), coef R v * ζ v) ^ 2) (LatticeProb.iidLaw d ν))
    (hI3 : ∀ R : ℝ, Integrable (fun ζ => (testedField (s R) (a R) (n R) ζ
        - (∫ η, testedField (s R) (a R) (n R) η ∂(LatticeProb.iidLaw d ν))
        - ∑ v ∈ testedSites (s R) (n R), coef R v * ζ v) ^ 2) (LatticeProb.iidLaw d ν)) :
    Tendsto (fun R : ℝ => ∫ ζ, (testedField (s R) (a R) (n R) ζ
        - (∫ η, testedField (s R) (a R) (n R) η ∂(LatticeProb.iidLaw d ν))
        - ∑ v ∈ testedSites (s R) (n R), coef R v * ζ v) ^ 2
      ∂(LatticeProb.iidLaw d ν)) l (𝓝 0) := by
  have hint : ∀ (R : ℝ) (v : Site d),
      (∫ η, rightDerivField (testedField (s R) (a R) (n R)) v η ∂(LatticeProb.iidLaw d ν))
        = ∫ η, (∑ x ∈ s R, a R x * odometerJacobian η (n R) x v)
            ∂(LatticeProb.iidLaw d ν) :=
    fun R v => integral_rightDerivField_testedField ν (s R) (a R) (n R) v
  have hvar : ∀ (R : ℝ) (v : Site d),
      variance (rightDerivField (testedField (s R) (a R) (n R)) v) (LatticeProb.iidLaw d ν)
        = variance (fun ζ => ∑ x ∈ s R, a R x * odometerJacobian ζ (n R) x v)
            (LatticeProb.iidLaw d ν) :=
    fun R v => variance_rightDerivField_testedField ν (s R) (a R) (n R) v
  exact tendsto_l2_testedField ν hmean hsq s a n ha coef B₀ hB₀
    (by simpa only [hvar] using hVar)
    (by simpa only [hint] using hcoef)
    (by simpa only [hint] using hI1)
    (by simpa only [hint] using hI2)
    hI3

end Sandpile
