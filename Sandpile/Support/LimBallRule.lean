import Sandpile.Support.LimBallValue
import Sandpile.Support.ExplBallLocal

/-!
# A ball-exit stopping rule lower-bounds the localized Brownian value

Shows that stopping Brownian motion at the first exit from an inner ball of radius `s ≤ A`,
truncated at a deterministic horizon `T`, is a legitimate stopping rule whose payoff bounds the
ball-localized value `brownianValueBall` from below, using only continuity of the paths and
boundedness of the attainable payoffs. The occupation-density identity behind the reward's exact
value and its limiting approximation are proved elsewhere.
-/

open MeasureTheory ProbabilityTheory Set Filter
open Sandpile.Continuum Sandpile.Support
open scoped ENNReal NNReal

/-- **Stopping at the first exit from an inner ball of radius `s`, truncated at the horizon
`T`, lower-bounds the ball-localized Brownian value.** For continuous paths and a reward `h`
with bounded attainable payoffs, `h T u` plus the expected reward collected at that stopping
time is at most `brownianValueBall B P h T A u`. -/
theorem Sandpile.Support.ballStopped_payoff_le {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (B : ℝ≥0 → Ω → Space d) (P : Measure Ω) (h : ℝ → Space d → ℝ)
    (T s A : ℝ) (u : Space d) (hT : 0 ≤ T) (hsA : s ≤ A)
    (hcont : ∀ ω, Continuous fun t => B t ω)
    (hbdd : BddAbove (ballStoppingPayoffs B P h T A u)) :
    h T u + (∫ ω, -h (T - (LatticeProb.exitTimeTrunc B u s T.toNNReal ω : ℝ))
      (B (LatticeProb.exitTimeTrunc B u s T.toNNReal ω) ω) ∂P) ≤
      brownianValueBall B P h T A u := by
  apply brownianValueBall_ge_of_rule B P h T A u (LatticeProb.exitTimeTrunc B u s T.toNNReal)
    (isBrownianStopping_exitTimeTrunc hcont u s T.toNNReal) _ _ hbdd
  · intro ω
    have hle : (LatticeProb.exitTimeTrunc B u s T.toNNReal ω : ℝ≥0∞) ≤
        (T.toNNReal : ℝ≥0∞) := by
      rw [LatticeProb.coe_exitTimeTrunc]
      exact inf_le_right
    have hle' : LatticeProb.exitTimeTrunc B u s T.toNNReal ω ≤ T.toNNReal := by exact_mod_cast hle
    have hle'' : (LatticeProb.exitTimeTrunc B u s T.toNNReal ω : ℝ) ≤ (T.toNNReal : ℝ) := by
      exact_mod_cast hle'
    simpa only [Real.coe_toNNReal T hT] using hle''
  · have hball := ball_condition_of_le_exitTime hcont u s
      (LatticeProb.exitTimeTrunc B u s T.toNNReal) (fun ω => by
        rw [LatticeProb.coe_exitTimeTrunc]
        exact inf_le_left)
    exact fun ω r hr => (hball ω r hr).trans hsA
