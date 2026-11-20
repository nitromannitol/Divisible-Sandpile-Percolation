import Sandpile.External.ContinuumOptimalStopping

/-!
# Superharmonic majorants of stopping values

A function that dominates the reward and is superharmonic along every bounded
stopping time dominates the corresponding stopping value.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- A superharmonic majorant of the reward dominates its stopping value. -/
theorem Sandpile.Support.snellValue_le_of_superharmonic_majorant
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (B : ℝ≥0 → Ω → Sandpile.Continuum.Space d)
    (T : ℝ≥0) (G F : ℝ → Sandpile.Continuum.Space d → ℝ) (v : ℝ)
    (hdom : ∀ t ∈ Set.Icc (0 : ℝ) (T : ℝ), ∀ y, G t y ≤ F t y)
    (hint : ∀ τ : Ω → ℝ≥0, Sandpile.Continuum.IsBrownianStopping B τ →
      (∀ ω, τ ω ≤ T) → Integrable (fun ω => G ((T : ℝ) - τ ω) (B (τ ω) ω)) P ∧
        Integrable (fun ω => F ((T : ℝ) - τ ω) (B (τ ω) ω)) P)
    (hsuper : ∀ τ : Ω → ℝ≥0, Sandpile.Continuum.IsBrownianStopping B τ →
      (∀ ω, τ ω ≤ T) → (∫ ω, F ((T : ℝ) - τ ω) (B (τ ω) ω) ∂P) ≤ v) :
    Sandpile.External.Snell.snellValue B P G T ≤ v := by
  have hne : (Sandpile.External.Snell.attainable B P G T).Nonempty := by
    refine ⟨∫ ω, G T (B 0 ω) ∂P, (fun _ => 0),
      Sandpile.Continuum.isBrownianStopping_const B 0, ?_, ?_⟩
    · intro ω
      exact T.coe_nonneg
    · simp only [NNReal.coe_zero, sub_zero]
  change sSup (Sandpile.External.Snell.attainable B P G T) ≤ v
  apply csSup_le hne
  rintro a ⟨τ, hτ, hτT, rfl⟩
  have hτT' : ∀ ω, τ ω ≤ T := fun ω => by exact_mod_cast hτT ω
  obtain ⟨hGi, hFi⟩ := hint τ hτ hτT'
  calc
    _ ≤ ∫ ω, F ((T : ℝ) - τ ω) (B (τ ω) ω) ∂P := by
      apply integral_mono_ae hGi hFi
      exact ae_of_all _ fun ω => hdom _
        ⟨sub_nonneg.mpr (by exact_mod_cast hτT' ω), sub_le_self _ (τ ω).coe_nonneg⟩ _
    _ ≤ v := hsuper τ hτ hτT'
