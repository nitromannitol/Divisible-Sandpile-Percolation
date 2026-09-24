/-
The matching of third moments between an exponential law and its centred
Gaussian counterpart, and the uniform inputs of the finite Lindeberg comparison.
The weighted moment and small-ball bounds used here are
`LatticeProb.Prob.ExponentialMoments`.
-/
import Sandpile.Support.FiniteLindeberg
import LatticeProb.Prob.ExponentialMoments

open LatticeProb

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Sandpile

lemma matchingThirdMoments_gaussian_of_exp {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {θ κ K : ℝ} (hθ : 0 < θ) (hκ : κ ≤ θ / 2)
    (hexp : Integrable (fun x : ℝ => Real.exp (θ * |x|)) μ)
    (hK : (∫ x : ℝ, Real.exp (θ * |x|) ∂μ) ≤ K)
    (hmean : (∫ x : ℝ, x ∂μ) = 0) (v : ℝ≥0)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂μ) = v) :
    MatchingThirdMoments μ (gaussianReal 0 v) κ
      ((48 / θ ^ 3) * max K (2 * Real.exp (2 * K))) := by
  have hv : (v : ℝ) ≤ (4 / θ ^ 2) * K := by
    rw [← hsecond]
    exact integral_sq_le_of_exp hθ hexp hK
  have hνK := integral_exp_abs_gaussian_le_of_variance_bound hθ v hv
  refine ⟨integrable_id_of_exp_moment μ θ hθ hexp,
    integrable_id_of_exp_moment _ θ hθ (integrable_exp_abs_gaussian θ v),
    integrable_sq_of_exp hθ hexp, integrable_sq_of_exp hθ (integrable_exp_abs_gaussian θ v),
    ?_, ?_, integrable_weighted_cube_of_exp hθ hκ hexp,
    integrable_weighted_cube_of_exp hθ hκ (integrable_exp_abs_gaussian θ v), ?_, ?_⟩
  · rw [hmean, integral_id_gaussianReal]
  · rw [hsecond, integral_sq_gaussian_zero]
  · exact integral_weighted_cube_le_of_exp hθ hκ hexp (hK.trans (le_max_left _ _))
  · exact integral_weighted_cube_le_of_exp hθ hκ (integrable_exp_abs_gaussian θ v)
      (hνK.trans (le_max_right _ _))

lemma exists_uniform_matching_gaussian_inputs (θ K : ℝ) (hθ : 0 < θ) :
    ∃ R > 0, ∃ T > 0, ∀ (μ : Measure ℝ), IsProbabilityMeasure μ →
      Integrable (fun x : ℝ => Real.exp (θ * |x|)) μ →
      (∫ x : ℝ, Real.exp (θ * |x|) ∂μ) ≤ K →
      (∫ x : ℝ, x ∂μ) = 0 → ∀ v : ℝ≥0, (∫ x : ℝ, x ^ 2 ∂μ) = v →
      ∀ κ : ℝ, κ ≤ θ / 2 →
        MatchingThirdMoments μ (gaussianReal 0 v) κ T ∧
        (1 / 2 : ℝ) ≤ μ.real (Icc (-R) R) ∧
        (1 / 2 : ℝ) ≤ (gaussianReal 0 v).real (Icc (-R) R) := by
  let L := max K (2 * Real.exp (2 * K))
  have hL : 0 < L := lt_of_lt_of_le (by positivity : 0 < 2 * Real.exp (2 * K)) (le_max_right _ _)
  refine ⟨2 * L / θ, by positivity, (48 / θ ^ 3) * L, by positivity, ?_⟩
  intro μ hμ hexp hK hmean v hsecond κ hκ
  letI : IsProbabilityMeasure μ := hμ
  refine ⟨matchingThirdMoments_gaussian_of_exp hθ hκ hexp hK hmean v hsecond, ?_, ?_⟩
  · exact small_ball_of_exp hθ hL hexp (hK.trans (le_max_left _ _))
  · have hv : (v : ℝ) ≤ (4 / θ ^ 2) * K := by
      rw [← hsecond]
      exact integral_sq_le_of_exp hθ hexp hK
    exact small_ball_of_exp hθ hL (integrable_exp_abs_gaussian θ v)
      ((integral_exp_abs_gaussian_le_of_variance_bound hθ v hv).trans (le_max_right _ _))

end Sandpile
