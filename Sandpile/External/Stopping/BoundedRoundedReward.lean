import Sandpile.External.Stopping.StepRewardIntegrable

/-!
# Rounding bounded step-walk rewards

Bounded measurable rewards are integrable at both the original and rounded
stopping times. The temporal modulus therefore bounds the change in expected
reward without an additional integrability assumption.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Sandpile.External.Stopping

/-- A bounded step-walk stop rounds to a bounded lattice stopping rule whose
expected reward differs by at most the given temporal modulus. -/
theorem exists_walkStopping_rounded_bounded_reward_le
    {d : ℕ} [NeZero d] {R : ℝ} (hR : 0 < R) (N : ℕ) (x : Site d)
    (T M ε : ℝ) (G : ℝ → Continuum.Space d → ℝ) (θ : (ℕ → Site d) → ℝ≥0)
    (hθ : Continuum.IsBrownianStopping (diffusiveStepWalk R) θ)
    (hθT : ∀ X, (θ X : ℝ) ≤ T)
    (hθN : ∀ X, θ X ≤ (N : ℝ≥0) / ⟨R ^ 2, sq_nonneg R⟩)
    (hGm : Measurable (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (hM : ∀ s z, |G s z| ≤ M)
    (hG : ∀ s ∈ Icc (0 : ℝ) T, ∀ u ∈ Icc (0 : ℝ) T, ∀ z,
      |s - u| < 1 / R ^ 2 → |G s z - G u z| ≤ ε) :
    ∃ κ : (ℕ → Site d) → ℕ, IsWalkStopping κ ∧ (∀ X, κ X ≤ N) ∧
      |(∫ X, G (T - θ X) (diffusiveStepWalk R (θ X) X) ∂(walkLaw d x)) -
        ∫ X, G (T - roundDiffusiveTime R hR (θ X)) (Lclt.scaledSite R (X (κ X)))
          ∂(walkLaw d x)| ≤ ε :=
  exists_walkStopping_rounded_reward_integral_le hR N x T ε G θ hθ hθT hθN hG
    (integrable_diffusiveStepWalk_stopped_reward R x T M G hGm hM θ hθ)
    (integrable_diffusiveStepWalk_rounded_reward hR x T M G hGm hM θ hθ)

end Sandpile.External.Stopping
