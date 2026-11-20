import Sandpile.Support.BrownianStoppedSupermartingale
import Sandpile.Support.SupermartingaleEqualExpectations

/-!
# Martingale property at an optimal stop

A bounded stopping time that preserves the expectation of the Brownian value
process makes the stopped value process a martingale.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- If a bounded Brownian stop preserves the expected value, the stopped value
process is a martingale. -/
theorem Sandpile.Support.brownian_value_stopped_martingale_of_integral_eq
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
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (LatticeProb.natFiltration (B x) (hBm x))
      (fun ω => (τ ω : ℝ≥0∞))) (hτT : ∀ ω, τ ω ≤ T)
    (hopt : (∫ ω, M (τ ω) ω ∂P) = ∫ ω, M 0 ω ∂P) :
    Martingale (fun s ω => M (min s (τ ω)) ω)
      (LatticeProb.natFiltration (B x) (hBm x)) P := by
  let 𝓕 := LatticeProb.natFiltration (B x) (hBm x)
  let N : ℝ≥0 → Ω → ℝ := fun s ω => M (min s (τ ω)) ω
  have hN : Supermartingale N 𝓕 P :=
    Sandpile.Support.brownian_value_stopped_supermartingale
      P B hB hBc hBm x T G hG hgrow M hMm hMc hMad hMval τ hτ hτT
  have hNT : (∫ ω, N T ω ∂P) = ∫ ω, N 0 ω ∂P := by
    simpa only [N, min_eq_right (hτT _), min_eq_left zero_le] using hopt
  apply Sandpile.Support.martingale_of_supermartingale_integral_eq P 𝓕 N hN
    (∫ ω, N 0 ω ∂P)
  intro s
  by_cases hsT : s ≤ T
  · have h0s := hN.setIntegral_le (show (0 : ℝ≥0) ≤ s from zero_le)
      (s := Set.univ) (@MeasurableSet.univ Ω (𝓕 0))
    have hsT' := hN.setIntegral_le hsT (s := Set.univ) (@MeasurableSet.univ Ω (𝓕 s))
    simp only [Measure.restrict_univ] at h0s hsT'
    linarith
  · have hTs : T ≤ s := le_of_not_ge hsT
    have he : N s = N T := by
      funext ω
      dsimp only [N]
      rw [min_eq_right ((hτT ω).trans hTs), min_eq_right (hτT ω)]
    rw [he, hNT]
