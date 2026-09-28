import Sandpile.Support.D4PointwiseTail
import Sandpile.Support.D4SubGaussianMoment

/-!
# Second Moment of the Dimension-Four Linearization Error

The second moment of the linearization error in dimension four, the estimate
Step 2 of `prop:d4-superdiffusive-limit` opens with (`sandpile.tex:3372`):

  `sup_{x ∈ Z^4} E E_t(x)^2 ≤ C (1 + log log t)`,   `E_t := u_t - E u_t(0) - V_t`.

The input is the concentration bound of `prop:d4-pointwise-linearization`,
`P(|E_t(x)| > λ) ≤ C exp(-c min(λ²/ℓ, λ))` with `ℓ := 1 + log log t`, which is
uniform in `x`. Integrating it over the level with the Gaussian branch below
the crossover `λ = ℓ` gives a bound LINEAR in `ℓ`; the exponential branch alone
would give `ℓ²`, a whole logarithm too weak. That integration is
`exists_square_bound_of_subgaussian_tail`.

The threshold `3 ≤ t` is what makes `ℓ ≥ 1`: it is `1 ≤ log t`, which needs
`e ≤ t`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Sandpile

/-- `1 ≤ 1 + log log t` for `3 ≤ t`, because `e < 3`. -/
lemma one_le_loglog_shift {t : ℕ} (ht : 3 ≤ t) : (1 : ℝ) ≤ 1 + Real.log (Real.log t) := by
  have h3 : (3 : ℝ) ≤ t := by exact_mod_cast ht
  have hexp : Real.exp 1 ≤ (t : ℝ) := by
    have := Real.exp_one_lt_d9
    linarith
  have hlog : (1 : ℝ) ≤ Real.log t :=
    (Real.le_log_iff_exp_le (by linarith : (0 : ℝ) < (t : ℝ))).mpr hexp
  have := Real.log_nonneg hlog
  linarith

/-- **The second moment of the linearization error is linear in `1 + log log t`**
(`sandpile.tex:3372`), uniformly in the site.  This is the first input of Step 2
of `prop:d4-superdiffusive-limit`. -/
theorem exists_second_moment_linearization_four (hVS : Sandpile.External.VarianceScale)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hmean : ∫ z, z ∂ν = 0)
    (θ : ℝ) (hθ : 0 < θ) (hexp : Integrable (fun z => Real.exp (θ * |z|)) ν) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℕ, 3 ≤ t → ∀ x : Sandpile.Site 4,
      Integrable (fun ζ => (odometerOf ζ t x -
          (∫ η, odometerOf η t 0 ∂(LatticeProb.iidLaw 4 ν)) - membrane ζ t x) ^ 2)
        (LatticeProb.iidLaw 4 ν) ∧
      (∫ ζ, (odometerOf ζ t x -
          (∫ η, odometerOf η t 0 ∂(LatticeProb.iidLaw 4 ν)) - membrane ζ t x) ^ 2
          ∂(LatticeProb.iidLaw 4 ν)) ≤ K * (1 + Real.log (Real.log t)) := by
  obtain ⟨c, C, hc, hC, hbound⟩ := exists_pointwise_linearization_four hVS ν hmean θ hθ hexp
  obtain ⟨K, hK, hsq⟩ :=
    exists_square_bound_of_subgaussian_tail (LatticeProb.iidLaw 4 ν) c C hc hC.le
  refine ⟨K, hK, fun t ht x => ?_⟩
  refine hsq _ ?_ _ (one_le_loglog_shift ht) (fun r hr => hbound t ht r hr.le x)
  exact ((measurable_odometerOf t x).sub measurable_const).sub (measurable_membrane t x)

end Sandpile
