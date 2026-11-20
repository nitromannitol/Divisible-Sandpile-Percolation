import Sandpile.Support.SnellSuperharmonicMajorant

/-!
# The superharmonic convexity argument

A convex combination of two superharmonic functions is superharmonic. If it
also dominates the reward, minimality of the stopping value compares the two
functions at the starting point.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- The convexity step in the superharmonic first-contact argument. -/
theorem Sandpile.Support.eq_of_superharmonic_convex_majorant
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (B : ℝ≥0 → Ω → Sandpile.Continuum.Space d)
    (T : ℝ≥0) (G V H : ℝ → Sandpile.Continuum.Space d → ℝ)
    (a ℓ : ℝ) (hℓ0 : 0 ≤ ℓ) (hℓ1 : ℓ < 1)
    (hdom : ∀ t ∈ Set.Icc (0 : ℝ) (T : ℝ), ∀ y,
      G t y ≤ ℓ * V t y + (1 - ℓ) * H t y)
    (hint : ∀ τ : Ω → ℝ≥0, Sandpile.Continuum.IsBrownianStopping B τ →
      (∀ ω, τ ω ≤ T) →
      Integrable (fun ω => G ((T : ℝ) - τ ω) (B (τ ω) ω)) P ∧
      Integrable (fun ω => V ((T : ℝ) - τ ω) (B (τ ω) ω)) P ∧
      Integrable (fun ω => H ((T : ℝ) - τ ω) (B (τ ω) ω)) P)
    (hV : ∀ τ : Ω → ℝ≥0, Sandpile.Continuum.IsBrownianStopping B τ →
      (∀ ω, τ ω ≤ T) → (∫ ω, V ((T : ℝ) - τ ω) (B (τ ω) ω) ∂P) ≤
        Sandpile.External.Snell.snellValue B P G T)
    (hH : ∀ τ : Ω → ℝ≥0, Sandpile.Continuum.IsBrownianStopping B τ →
      (∀ ω, τ ω ≤ T) → (∫ ω, H ((T : ℝ) - τ ω) (B (τ ω) ω) ∂P) ≤ a)
    (ha : a ≤ Sandpile.External.Snell.snellValue B P G T) :
    a = Sandpile.External.Snell.snellValue B P G T := by
  let F : ℝ → Sandpile.Continuum.Space d → ℝ := fun t y => ℓ * V t y + (1 - ℓ) * H t y
  have hFi : ∀ τ : Ω → ℝ≥0, Sandpile.Continuum.IsBrownianStopping B τ →
      (∀ ω, τ ω ≤ T) → Integrable (fun ω => G ((T : ℝ) - τ ω) (B (τ ω) ω)) P ∧
        Integrable (fun ω => F ((T : ℝ) - τ ω) (B (τ ω) ω)) P := by
    intro τ hτ hτT
    obtain ⟨hGi, hVi, hHi⟩ := hint τ hτ hτT
    exact ⟨hGi, (hVi.const_mul ℓ).add (hHi.const_mul (1 - ℓ))⟩
  have hFsuper : ∀ τ : Ω → ℝ≥0, Sandpile.Continuum.IsBrownianStopping B τ →
      (∀ ω, τ ω ≤ T) →
      (∫ ω, F ((T : ℝ) - τ ω) (B (τ ω) ω) ∂P) ≤
        ℓ * Sandpile.External.Snell.snellValue B P G T + (1 - ℓ) * a := by
    intro τ hτ hτT
    obtain ⟨_, hVi, hHi⟩ := hint τ hτ hτT
    change (∫ ω, ℓ * V ((T : ℝ) - τ ω) (B (τ ω) ω) +
      (1 - ℓ) * H ((T : ℝ) - τ ω) (B (τ ω) ω) ∂P) ≤ _
    rw [integral_add (hVi.const_mul ℓ) (hHi.const_mul (1 - ℓ)),
      integral_const_mul, integral_const_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left (hV τ hτ hτT) hℓ0)
      (mul_le_mul_of_nonneg_left (hH τ hτ hτT) (sub_nonneg.mpr hℓ1.le))
  have hbound := Sandpile.Support.snellValue_le_of_superharmonic_majorant P B T G F
    (ℓ * Sandpile.External.Snell.snellValue B P G T + (1 - ℓ) * a) hdom hFi hFsuper
  apply le_antisymm ha
  nlinarith
