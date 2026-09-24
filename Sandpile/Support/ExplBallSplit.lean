/-
Where the capped time differs from the time.

The proof of `lem:localization-killing` (`sandpile.tex:1624-1629`) splits at the
first exit and pays only on the event `{τ_D < τ}`.  In the continuum that event
is `{τ_{u,A} < τ}`, and for a stopping time bounded by the horizon it sits inside
the event that the ball is left before the horizon, whose probability is the
exit-time tail.  These two facts are what turns the split of a single stopping
time into the factor `C e^{-cA²/T}` of `lem:brownian-ball-localization`.
-/
import Sandpile.Support.ExplBallGap

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Sandpile.Continuum

variable {ΩB : Type*} [MeasurableSpace ΩB] {d : ℕ}

/-- Monotonicity of the real-valued measure of an arbitrary pair of sets, read through the
outer measure, which is all the split needs. -/
theorem measureReal_mono_of_subset (P : Measure ΩB) [IsFiniteMeasure P] (E F : Set ΩB)
    (hsub : E ⊆ F) : P.real E ≤ P.real F := by
  have h0 : P E ≤ P F := measure_mono hsub
  calc P.real E = (P E).toReal := rfl
    _ ≤ (P F).toReal := ENNReal.toReal_mono (measure_ne_top P F) h0
    _ = P.real F := rfl

omit [MeasurableSpace ΩB] in
/-- The event on which the capped time differs from the time, `{τ_{u,A} < τ}`, is contained in
the event that the ball is left before the horizon. -/
theorem lt_subset_ballExitEvent (B : ℝ≥0 → ΩB → Space d) (u : Space d) (A T : ℝ) (hT : 0 < T)
    (hcont : ∀ ω, Continuous fun s => B s ω) (τ : ΩB → ℝ≥0) (hbound : ∀ ω, (τ ω : ℝ) ≤ T) :
    {ω : ΩB | ballExitTime B u A T ω < τ ω} ⊆ ballExitEvent B u A T := by
  intro ω hω
  have h1 : ballExitTime B u A T ω < τ ω := hω
  have h2 : ((ballExitTime B u A T ω : ℝ≥0) : ℝ) < ((τ ω : ℝ≥0) : ℝ) := by exact_mod_cast h1
  have h3 : ((ballExitTime B u A T ω : ℝ≥0) : ℝ) < T := lt_of_lt_of_le h2 (hbound ω)
  rw [ballExitEvent_eq B u A T hT hcont]
  exact h3

/-- The probability of the event where the capped time differs from the time is at most the
exit-time tail. -/
theorem measureReal_lt_le_ballExitEvent (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    [IsFiniteMeasure P] (u : Space d) (A T : ℝ) (hT : 0 < T)
    (hcont : ∀ ω, Continuous fun s => B s ω) (τ : ΩB → ℝ≥0) (hbound : ∀ ω, (τ ω : ℝ) ≤ T) :
    P.real {ω : ΩB | ballExitTime B u A T ω < τ ω} ≤ P.real (ballExitEvent B u A T) :=
  measureReal_mono_of_subset P _ _ (lt_subset_ballExitEvent B u A T hT hcont τ hbound)

end Sandpile.Continuum
