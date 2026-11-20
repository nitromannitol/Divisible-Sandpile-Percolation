import Sandpile.Support.BrownianValueContinuity
import Sandpile.Support.ValueProcessFirstContact

/-!
# Brownian value process and first contact

A polynomial-growth Brownian stopping value has a measurable continuous value
process and a pointwise least natural-filtration contact time.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- Brownian stopping values produce a measurable continuous value process and
a pointwise least natural-filtration contact time. -/
theorem Sandpile.Support.exists_brownian_snell_value_process_first_contact
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Sandpile.Continuum.Space d → ℝ≥0 → Ω → Sandpile.Continuum.Space d)
    (hB : ∀ y, Sandpile.Continuum.IsBrownian d y (B y) P)
    (hBc : ∀ y ω, Continuous fun t => B y t ω)
    (hBm : ∀ y t, StronglyMeasurable (B y t))
    (x : Sandpile.Continuum.Space d) (T : ℝ≥0)
    (G : ℝ → Sandpile.Continuum.Space d → ℝ)
    (hG : ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2)
      (Set.Icc 0 (T : ℝ) ×ˢ Set.univ))
    (hgrow : ∃ C k : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) (T : ℝ),
      ∀ y, |G t y| ≤ C * (1 + ‖y‖) ^ k) :
    ∃ M : ℝ≥0 → Ω → ℝ,
      (∀ s, Measurable (M s)) ∧
      (∀ s ≤ T, ∀ ω, M s ω =
        Sandpile.External.Snell.snellValue (B (B x s ω)) P G ((T : ℝ) - s)) ∧
      (∀ ω, Continuous fun s => M s ω) ∧
      ∃ τ : Ω → ℝ≥0,
        (∀ ω, IsLeast {s : ℝ≥0 | s ≤ T ∧
          M s ω = G ((T : ℝ) - s) (B x s ω)} (τ ω)) ∧
        Sandpile.Continuum.IsBrownianStopping (B x) τ := by
  exact Sandpile.Support.exists_snell_value_process_first_contact_of_continuous
    P B hB x (hBc x) (hBm x) T G hG
    (Sandpile.Support.continuousOn_brownian_snellValue P B hB hBm hBc T G hG hgrow)
