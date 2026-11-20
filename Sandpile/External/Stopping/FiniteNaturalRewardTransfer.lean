import Sandpile.External.Stopping.FiniteNaturalStopTransfer
import Sandpile.External.Stopping.StepRewardIntegrable

/-!
# Finite natural stopping rewards under pushforward laws

Finite stopping rules factor through a measurable process map, and their
expected rewards transfer along the corresponding pushforward measure.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- Finite natural stopping rewards transfer from a process realization to its
pushforward process law. -/
theorem exists_finite_natural_reward_factor
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {d : ℕ}
    (P : Measure Ω) (Q : Measure Ξ)
    (Z : ℝ≥0 → Ξ → Continuum.Space d) (hZm : ∀ t, StronglyMeasurable (Z t))
    (hZjoint : Measurable (fun p : ℝ≥0 × Ξ => Z p.1 p.2))
    (f : Ω → Ξ) (hf : Measurable f) (hQ : P.map f = Q)
    (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτ : Continuum.IsBrownianStopping (fun s ω => Z s (f ω)) τ)
    (hτT : ∀ ω, τ ω ≤ T) (hτfin : (Set.range τ).Finite)
    (G : ℝ≥0 → Continuum.Space d → ℝ)
    (hG : Measurable (fun p : ℝ≥0 × Continuum.Space d => G p.1 p.2)) :
    ∃ σ : Ξ → ℝ≥0, Continuum.IsBrownianStopping Z σ ∧
      (∀ ξ, σ ξ ≤ T) ∧ (Set.range σ).Finite ∧
      (∫ ω, G (τ ω) (Z (τ ω) (f ω)) ∂P) = ∫ ξ, G (σ ξ) (Z (σ ξ) ξ) ∂Q := by
  obtain ⟨σ, hσ, hσT, hσfin, hτσ⟩ :=
    exists_finite_natural_stopping_factor Z hZm f hf T τ hτ hτT hτfin
  have hσm : Measurable σ := measurable_of_isBrownianStopping Z (fun t => (hZm t).measurable) σ hσ
  have hpos : Measurable (fun ξ => Z (σ ξ) ξ) := hZjoint.comp (hσm.prodMk measurable_id)
  have hreward : Measurable (fun ξ => G (σ ξ) (Z (σ ξ) ξ)) := hG.comp (hσm.prodMk hpos)
  refine ⟨σ, hσ, hσT, hσfin, ?_⟩
  have heq : (fun ω => G (τ ω) (Z (τ ω) (f ω))) =
      (fun ω => G (σ (f ω)) (Z (σ (f ω)) (f ω))) := by
    funext ω
    rw [hτσ ω]
  rw [heq, ← MeasureTheory.integral_map hf.aemeasurable hreward.aestronglyMeasurable, hQ]

end Sandpile.External.Stopping
