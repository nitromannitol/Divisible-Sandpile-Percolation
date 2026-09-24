/-
The payoff of Brownian motion stopped at a deterministic horizon or the first
exit from a smaller ball bounds the localized value from below.
Continuity of all paths and boundedness of the attainable payoffs are explicit;
the occupation-density identity and its limiting approximation are separate.
-/
import Sandpile.Support.LimBallValue
import Sandpile.Support.ExplBallLocal
open MeasureTheory ProbabilityTheory Set Filter
open Sandpile.Continuum Sandpile.Support
open scoped ENNReal NNReal

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
