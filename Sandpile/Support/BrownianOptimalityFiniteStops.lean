import Sandpile.Support.BrownianOptimalityReduction
import Sandpile.Support.StoppedExpectationExtension

/-!
# Optimal stopping from finite-range expectation bounds

For a continuous dominated Brownian value process, a stopped expectation
bound at finitely valued stopping times extends to all bounded stopping times.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- The stopped martingale property and the expectation bound at finite-range
stops imply optimality and minimality of the first contact. -/
theorem Sandpile.Support.first_contact_greatest_and_minimal_of_finite_stops
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
      ∀ y, |G t y| ≤ C * (1 + ‖y‖) ^ k)
    (M : ℝ≥0 → Ω → ℝ) (hMm : ∀ s, Measurable (M s))
    (hMc : ∀ ω, Continuous fun s => M s ω)
    (hMval : ∀ s ≤ T, ∀ ω, M s ω =
      Sandpile.External.Snell.snellValue (B (B x s ω)) P G ((T : ℝ) - s))
    (hMdom : ∀ s ≤ T, ∀ ω, G ((T : ℝ) - s) (B x s ω) ≤ M s ω)
    (τ : Ω → ℝ≥0)
    (hfirst : ∀ ω, IsLeast {s : ℝ≥0 | s ≤ T ∧
      M s ω = G ((T : ℝ) - s) (B x s ω)} (τ ω))
    (hτstop : Sandpile.Continuum.IsBrownianStopping (B x) τ)
    (hmart : Martingale (fun s ω => M (min s (τ ω)) ω)
      (LatticeProb.natFiltration (B x) (hBm x)) P)
    (hfinite : ∀ σ : Ω → ℝ≥0, Sandpile.Continuum.IsBrownianStopping (B x) σ →
      (Set.range σ).Finite → (∀ ω, σ ω ≤ T) →
      (∫ ω, M (σ ω) ω ∂P) ≤ Sandpile.External.Snell.snellValue (B x) P G T) :
    IsGreatest (Sandpile.External.Snell.attainable (B x) P G T)
      (∫ ω, G ((T : ℝ) - τ ω) (B x (τ ω) ω) ∂P) ∧
    ∀ σ : Ω → ℝ≥0, Sandpile.Continuum.IsBrownianStopping (B x) σ →
      (∀ ω, σ ω ≤ T) →
      (∫ ω, G ((T : ℝ) - σ ω) (B x (σ ω) ω) ∂P) =
        Sandpile.External.Snell.snellValue (B x) P G T →
      ∀ᵐ ω ∂P, τ ω ≤ σ ω := by
  obtain ⟨D, hDi, hD, _⟩ :=
    Sandpile.Support.exists_integrable_brownian_value_process_bound
      P B hB hBc hBm x T G hG hgrow M hMm hMc hMval
  apply Sandpile.Support.first_contact_greatest_and_minimal_of_stopped_martingale
    P B hB hBc hBm x T G hG hgrow M hMm hMc hMval hMdom τ hfirst hτstop hmart
  intro σ hσ hσT
  exact Sandpile.Support.stopped_expectation_le_of_finite_range P
    (LatticeProb.natFiltration (B x) (hBm x)) M (fun s => (hMm s).stronglyMeasurable)
    hMc T D hDi hD _ hfinite σ hσ hσT
