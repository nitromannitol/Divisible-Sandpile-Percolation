import Sandpile.Support.BrownianPolynomialReward

/-!
# The Brownian stopping value dominates the gain

Stopping immediately shows that the finite-horizon value is at least the
reward at the starting point.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- A Brownian stopping value dominates the reward from immediate stopping. -/
theorem Sandpile.Support.le_brownian_snellValue
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (x : Sandpile.Continuum.Space d)
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → Sandpile.Continuum.Space d)
    (hB : Sandpile.Continuum.IsBrownian d x B P)
    (hBm : ∀ t, StronglyMeasurable (B t)) (hBc : ∀ ω, Continuous fun t => B t ω)
    (T : ℝ≥0) (G : ℝ → Sandpile.Continuum.Space d → ℝ)
    (hG : ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2)
      (Set.Icc 0 (T : ℝ) ×ˢ Set.univ))
    (hgrow : ∃ C k : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) (T : ℝ),
      ∀ y, |G t y| ≤ C * (1 + ‖y‖) ^ k) :
    G T x ≤ Sandpile.External.Snell.snellValue B P G T := by
  have hbdd := (Sandpile.Support.brownian_stopping_payoffs_integrable_and_bddAbove
    x P B hB hBm hBc T G hG hgrow).2
  have hpay : (∫ ω, G T (B 0 ω) ∂P) = G T x := by
    calc
      _ = ∫ _ω, G T x ∂P := by
        apply integral_congr_ae
        filter_upwards [hB.start] with ω hω
        rw [hω]
      _ = _ := by simp
  have hmem : (∫ ω, G T (B 0 ω) ∂P) ∈ Sandpile.External.Snell.attainable B P G T := by
    refine ⟨fun _ => 0, Sandpile.Continuum.isBrownianStopping_const B 0, ?_, ?_⟩
    · intro ω
      exact T.coe_nonneg
    · simp only [NNReal.coe_zero, sub_zero]
  change G T x ≤ sSup (Sandpile.External.Snell.attainable B P G T)
  rw [← hpay]
  exact le_csSup hbdd hmem
