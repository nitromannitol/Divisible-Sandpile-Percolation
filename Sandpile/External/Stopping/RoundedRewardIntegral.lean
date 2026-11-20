import Sandpile.External.Stopping.RoundedStepReward

/-!
# Expected rewards at rounded step-walk stops

A bounded step-walk stopping time rounds to a bounded lattice stopping rule.
If its original and rounded rewards are integrable, a temporal modulus gives
the same bound on their expected difference.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- Rounding a bounded step-walk stopping time yields a bounded discrete
stopping rule and changes its expected reward by at most the temporal modulus,
provided both rewards are integrable. -/
theorem exists_walkStopping_rounded_reward_integral_le
    {d : ℕ} [NeZero d] {R : ℝ} (hR : 0 < R) (N : ℕ) (x : Site d)
    (T ε : ℝ) (G : ℝ → Continuum.Space d → ℝ) (θ : (ℕ → Site d) → ℝ≥0)
    (hθ : Continuum.IsBrownianStopping (diffusiveStepWalk R) θ)
    (hθT : ∀ X, (θ X : ℝ) ≤ T)
    (hθN : ∀ X, θ X ≤ (N : ℝ≥0) / ⟨R ^ 2, sq_nonneg R⟩)
    (hG : ∀ s ∈ Icc (0 : ℝ) T, ∀ u ∈ Icc (0 : ℝ) T, ∀ z,
      |s - u| < 1 / R ^ 2 → |G s z - G u z| ≤ ε)
    (hI₁ : Integrable (fun X => G (T - θ X) (diffusiveStepWalk R (θ X) X)) (walkLaw d x))
    (hI₂ : Integrable (fun X => G (T - roundDiffusiveTime R hR (θ X))
      (Lclt.scaledSite R (X (diffusiveTimeIndex R (θ X))))) (walkLaw d x)) :
    ∃ κ : (ℕ → Site d) → ℕ, IsWalkStopping κ ∧ (∀ X, κ X ≤ N) ∧
      |(∫ X, G (T - θ X) (diffusiveStepWalk R (θ X) X) ∂(walkLaw d x)) -
        ∫ X, G (T - roundDiffusiveTime R hR (θ X)) (Lclt.scaledSite R (X (κ X)))
          ∂(walkLaw d x)| ≤ ε := by
  let κ : (ℕ → Site d) → ℕ := fun X => diffusiveTimeIndex R (θ X)
  have hκ : IsWalkStopping κ := isWalkStopping_floor_of_diffusiveStepWalk hR θ hθ
  have hκN : ∀ X, κ X ≤ N := fun X => diffusiveTimeIndex_le_of_le_grid hR (θ X) N (hθN X)
  refine ⟨κ, hκ, hκN, ?_⟩
  let : IsProbabilityMeasure (walkLaw d x) := by
    change IsProbabilityMeasure (LatticeProb.siteWalkLaw d x)
    infer_instance
  have hpoint : ∀ᵐ X ∂(walkLaw d x),
      ‖G (T - θ X) (diffusiveStepWalk R (θ X) X) -
        G (T - roundDiffusiveTime R hR (θ X)) (Lclt.scaledSite R (X (κ X)))‖ ≤ ε := by
    filter_upwards with X
    simpa only [Real.norm_eq_abs, κ] using
      abs_stepWalk_reward_sub_rounded_le hR T ε G (θ X) (hθT X) X hG
  have hb := norm_integral_le_of_norm_le_const hpoint
  rw [← integral_sub hI₁ hI₂, ← Real.norm_eq_abs]
  simpa using hb

end Sandpile.External.Stopping
