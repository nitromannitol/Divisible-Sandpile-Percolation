import Sandpile.External.ContinuumOptimalStopping

/-!
# Optimal stopping for continuous Brownian paths

The finite-horizon optimal-stopping input with continuity of every sample path.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- The finite-horizon optimal-stopping input for a Brownian family whose paths
are all continuous. -/
def Sandpile.External.ContinuumOptimalStoppingOfContinuous (Ω : Type*) [MeasurableSpace Ω] : Prop :=
  ∀ (d : ℕ) (T : ℝ), 0 < T →
    ∀ G : ℝ → Sandpile.Continuum.Space d → ℝ,
      ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2)
        (Set.Icc 0 T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d))) →
      (∃ C k : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T,
        ∀ y : Sandpile.Continuum.Space d, |G t y| ≤ C * (1 + ‖y‖) ^ k) →
      ∀ x : Sandpile.Continuum.Space d,
        ∀ (P : Measure Ω) [IsProbabilityMeasure P]
          (B : Sandpile.Continuum.Space d → ℝ≥0 → Ω → Sandpile.Continuum.Space d),
          (∀ y : Sandpile.Continuum.Space d, Sandpile.Continuum.IsBrownian d y (B y) P) →
          (∀ y ω, Continuous fun s => B y s ω) →
          ∃ M : ℝ≥0 → Ω → ℝ,
            (∀ s : ℝ≥0, Measurable (M s)) ∧
            (∀ s : ℝ≥0, (s : ℝ) ≤ T →
              M s =ᵐ[P] fun ω =>
                Sandpile.External.Snell.snellValue (B (B x s ω)) P G (T - (s : ℝ))) ∧
            (∀ (ω : Ω) (s : ℝ≥0),
              ContinuousWithinAt (fun r : ℝ≥0 => M r ω) (Set.Ici s) s) ∧
            ∃ τ : Ω → ℝ≥0,
              (∀ ω : Ω, IsLeast {s : ℝ≥0 | (s : ℝ) ≤ T ∧
                M s ω = G (T - (s : ℝ)) (B x s ω)} (τ ω)) ∧
              Sandpile.Continuum.IsBrownianStopping (B x) τ ∧
              IsGreatest (Sandpile.External.Snell.attainable (B x) P G T)
                (∫ ω, G (T - (τ ω : ℝ)) (B x (τ ω) ω) ∂P) ∧
              ∀ τ' : Ω → ℝ≥0, Sandpile.Continuum.IsBrownianStopping (B x) τ' →
                (∀ ω : Ω, (τ' ω : ℝ) ≤ T) →
                (∫ ω, G (T - (τ' ω : ℝ)) (B x (τ' ω) ω) ∂P) =
                  Sandpile.External.Snell.snellValue (B x) P G T →
                ∀ᵐ ω ∂P, τ ω ≤ τ' ω

/-- The original input implies the version for everywhere continuous paths. -/
theorem Sandpile.External.continuumOptimalStoppingOfContinuous_of_continuumOptimalStopping
    {Ω : Type*} [MeasurableSpace Ω] (h : Sandpile.External.ContinuumOptimalStopping Ω) :
    Sandpile.External.ContinuumOptimalStoppingOfContinuous Ω := by
  intro d T hT G hG hGgrow x P _ B hB _
  exact h d T hT G hG hGgrow x P B hB
