import Sandpile.Support.ExplStability

/-!
# The Brownian value is Lipschitz in the field

The Brownian optimal-stopping value `brownianValue` reads its reward field `h` only through
the restriction of `h` to `[0, t] × Space d`, so two fields within `E` of each other in the
supremum norm on `[0, T] × Space d` give values within `2E`
(`abs_brownianValue_sub_le_of_field`), with the sharper `E = 1` case
`abs_brownianValue_sub_le_one` used below. This quantitative Lipschitz bound is what lets a
continuous modification of the Gaussian heat potential replace the potential itself in the
value, and what makes the value a continuous functional of the field.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped NNReal ENNReal
open Sandpile.Continuum

namespace Sandpile.Support

/-- **The Brownian value is Lipschitz in the field.**  Two fields uniformly within
`E` on `[0,T] × ℝ^d` give values within `2E`. -/
theorem abs_brownianValue_sub_le_of_field {ΩB : Type*} [MeasurableSpace ΩB]
    (d : ℕ) (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB) [IsProbabilityMeasure P]
    (h h' : ℝ → Space d → ℝ) (T E : ℝ) (hT : 0 ≤ T) (x : Space d)
    (hbdd : BddAbove (stoppingPayoffs B P h T))
    (hbdd' : BddAbove (stoppingPayoffs B P h' T))
    (hint : ∀ τ : ΩB → ℝ≥0, IsBrownianStopping B τ → (∀ ω, (τ ω : ℝ) ≤ T) →
      Integrable (fun ω => -h (T - τ ω) (B (τ ω) ω)) P)
    (hint' : ∀ τ : ΩB → ℝ≥0, IsBrownianStopping B τ → (∀ ω, (τ ω : ℝ) ≤ T) →
      Integrable (fun ω => -h' (T - τ ω) (B (τ ω) ω)) P)
    (hgap : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ y : Space d, |h s y - h' s y| ≤ E) :
    |brownianValue B P h T x - brownianValue B P h' T x| ≤ 2 * E := by
  have h1 : |h T x - h' T x| ≤ E := hgap T ⟨hT, le_refl T⟩ x
  have h2 : |brownianDiscount B P h T - brownianDiscount B P h' T| ≤ E :=
    Sandpile.Continuum.abs_brownianDiscount_sub_le_of_reward B P h h' T E hT hbdd hbdd'
      hint hint' hgap
  have h1a : -(E) ≤ h T x - h' T x := (abs_le.mp h1).1
  have h1b : h T x - h' T x ≤ E := (abs_le.mp h1).2
  have h2a : -(E) ≤ brownianDiscount B P h T - brownianDiscount B P h' T := (abs_le.mp h2).1
  have h2b : brownianDiscount B P h T - brownianDiscount B P h' T ≤ E := (abs_le.mp h2).2
  unfold brownianValue
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- **The value is `2`-Lipschitz in the field, in the unit sup norm.**  The
`E = 1` case of `abs_brownianValue_sub_le_of_field`, which is the form the
continuous-functional argument uses. -/
theorem abs_brownianValue_sub_le_one {ΩB : Type*} [MeasurableSpace ΩB]
    (d : ℕ) (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB) [IsProbabilityMeasure P]
    (T : ℝ) (hT : 0 ≤ T) (x : Space d)
    (hbdd : ∀ h : ℝ → Space d → ℝ, BddAbove (stoppingPayoffs B P h T))
    (hint : ∀ (h : ℝ → Space d → ℝ), (∀ s ∈ Set.Icc (0:ℝ) T, ∀ _y : Space d,
        ∀ τ : ΩB → ℝ≥0, IsBrownianStopping B τ → (∀ ω, (τ ω : ℝ) ≤ T) →
          Integrable (fun ω => -h (T - τ ω) (B (τ ω) ω)) P))
    (v w : ℝ → Space d → ℝ)
    (hgap : ∀ s ∈ Set.Icc (0:ℝ) T, ∀ y : Space d, |v s y - w s y| ≤ 1) :
    |brownianValue B P v T x - brownianValue B P w T x| ≤ 2 := by
  simpa using Sandpile.Support.abs_brownianValue_sub_le_of_field d B P v w T 1 hT x
    (hbdd v) (hbdd w)
    (fun τ hτ hb => hint v 0 ⟨le_refl 0, hT⟩ x τ hτ hb)
    (fun τ hτ hb => hint w 0 ⟨le_refl 0, hT⟩ x τ hτ hb)
    hgap

end Sandpile.Support
