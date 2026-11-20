import Sandpile.Support.BrownianFirstContactOptimal
import Sandpile.Support.BrownianOptimalStopMartingale

/-!
# Brownian value martingale up to first contact

The Brownian value process stopped at its first contact with the reward is a
martingale.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- The Brownian value process stopped at first contact is a martingale in the
raw natural filtration. -/
theorem Sandpile.Support.brownian_first_contact_stopped_martingale
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
    (hMad : StronglyAdapted (LatticeProb.natFiltration (B x) (hBm x)) M)
    (hMval : ∀ s ≤ T, ∀ ω, M s ω =
      Sandpile.External.Snell.snellValue (B (B x s ω)) P G ((T : ℝ) - s))
    (hMdom : ∀ s ≤ T, ∀ ω, G ((T : ℝ) - s) (B x s ω) ≤ M s ω)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (LatticeProb.natFiltration (B x) (hBm x))
      (fun ω => (τ ω : ℝ≥0∞)))
    (hfirst : ∀ ω, IsLeast {s : ℝ≥0 | s ≤ T ∧
      M s ω = G ((T : ℝ) - s) (B x s ω)} (τ ω)) :
    Martingale (fun s ω => M (min s (τ ω)) ω)
      (LatticeProb.natFiltration (B x) (hBm x)) P := by
  have hopt := Sandpile.Support.brownian_first_contact_optimal
    P B hB hBc hBm x T G hG hgrow M hMm hMc hMad hMval hMdom τ hfirst
  have hinit := Sandpile.Support.integral_brownian_value_process_zero P B x (hB x) T G M hMval
  have hvalue : (∫ ω, M (τ ω) ω ∂P) = ∫ ω, M 0 ω ∂P := by
    calc
      _ = ∫ ω, G ((T : ℝ) - τ ω) (B x (τ ω) ω) ∂P := by
        apply integral_congr_ae
        exact ae_of_all P fun ω => (hfirst ω).1.2
      _ = _ := hopt.trans hinit.symm
  exact Sandpile.Support.brownian_value_stopped_martingale_of_integral_eq
    P B hB hBc hBm x T G hG hgrow M hMm hMc hMad hMval τ hτ
    (fun ω => (hfirst ω).1.1) hvalue
