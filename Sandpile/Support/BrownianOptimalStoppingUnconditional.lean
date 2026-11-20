import Sandpile.Frozen.BrownianOptimalStopping
import Sandpile.External.ContinuumOptimalStoppingProved

/-!
# Brownian optimal-stopping representation without hypotheses

`prop:brownian-os` holds without its optimal-stopping hypothesis: the finite-horizon
optimal-stopping theorem for Brownian motion is supplied by
`Sandpile.External.continuumOptimalStopping_holds`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- The Brownian optimal-stopping representation. -/
-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.brownian_optimal_stopping_proved
    (d : ℕ) (T : ℝ) (hT : 0 < T) (h : ℝ → Sandpile.Continuum.Space d → ℝ)
    (hcont : ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => h p.1 p.2)
      (Set.Icc 0 T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d))))
    (hgrow : ∃ C k : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ y : Sandpile.Continuum.Space d, |h t y| ≤ C * (1 + ‖y‖) ^ k)
    (x : Sandpile.Continuum.Space d)
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Sandpile.Continuum.Space d → ℝ≥0 → Ω → Sandpile.Continuum.Space d)
    (hB : ∀ y : Sandpile.Continuum.Space d, Sandpile.Continuum.IsBrownian d y (B y) P)
    (hBc : ∀ y ω, Continuous fun s => B y s ω)
    (hBm : ∀ y t, StronglyMeasurable (B y t)) :
    ∃ M : ℝ≥0 → Ω → ℝ,
      (∀ s : ℝ≥0, Measurable (M s)) ∧
      (∀ s : ℝ≥0, (s : ℝ) ≤ T →
        M s =ᵐ[P] fun ω =>
          Sandpile.Continuum.brownianDiscount (B (B x s ω)) P h (T - (s : ℝ))) ∧
      (∀ (ω : Ω) (s : ℝ≥0),
        ContinuousWithinAt (fun r : ℝ≥0 => M r ω) (Set.Ici s) s) ∧
      ∃ τ : Ω → ℝ≥0,
        (∀ ω : Ω, IsLeast {s : ℝ≥0 | (s : ℝ) ≤ T ∧
          h (T - (s : ℝ)) (B x s ω) + M s ω = 0} (τ ω)) ∧
        Sandpile.Continuum.IsBrownianStopping (B x) τ ∧
        Sandpile.Continuum.brownianValue (B x) P h T x =
          h T x - ∫ ω, h (T - (τ ω : ℝ)) (B x (τ ω) ω) ∂P ∧
        (∀ τ' : Ω → ℝ≥0, Sandpile.Continuum.IsBrownianStopping (B x) τ' →
          (∀ ω : Ω, (τ' ω : ℝ) ≤ T) →
          Sandpile.Continuum.brownianValue (B x) P h T x =
            h T x - ∫ ω, h (T - (τ' ω : ℝ)) (B x (τ' ω) ω) ∂P →
          ∀ᵐ ω ∂P, τ ω ≤ τ' ω) ∧
        Sandpile.Continuum.brownianValue (B x) P h T x =
          sSup {a : ℝ | ∃ σ : Ω → ℝ≥0, Sandpile.Continuum.IsBrownianStopping (B x) σ ∧
            (∀ ω : Ω, (σ ω : ℝ) ≤ T) ∧
            a = h T x - ∫ ω, h (T - (σ ω : ℝ)) (B x (σ ω) ω) ∂P}
-- FROZEN-STATEMENT-END
:=
  Sandpile.Frozen.brownian_optimal_stopping d T hT h hcont hgrow x
    Sandpile.External.continuumOptimalStopping_holds P B hB hBc hBm
