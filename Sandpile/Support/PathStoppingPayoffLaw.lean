import Sandpile.Support.PathStoppingFunctional
import Sandpile.Support.StopMeasurable
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-!
# Stopped payoffs and continuous path laws

Processes with the same continuous-path law give the same payoff when stopped
by a common bounded measurable path functional.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- Equal continuous-path laws give equal payoffs for a bounded measurable
stopping functional and a continuous finite-horizon reward. -/
theorem Sandpile.Support.integral_path_stopping_payoff_eq_of_law
    {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {d : ℕ}
    (P₁ : Measure Ω₁) (P₂ : Measure Ω₂)
    (B₁ : ℝ≥0 → Ω₁ → Sandpile.Continuum.Space d)
    (B₂ : ℝ≥0 → Ω₂ → Sandpile.Continuum.Space d)
    (hBm₁ : ∀ t, StronglyMeasurable (B₁ t)) (hBm₂ : ∀ t, StronglyMeasurable (B₂ t))
    (hBc₁ : ∀ ω, Continuous fun t => B₁ t ω) (hBc₂ : ∀ ω, Continuous fun t => B₂ t ω)
    (hlaw : P₁.map (fun ω => (⟨fun t => B₁ t ω, hBc₁ ω⟩ : C(ℝ≥0, Sandpile.Continuum.Space d))) =
      P₂.map (fun ω => (⟨fun t => B₂ t ω, hBc₂ ω⟩ : C(ℝ≥0, Sandpile.Continuum.Space d))))
    (T : ℝ≥0) (G : ℝ → Sandpile.Continuum.Space d → ℝ)
    (hG : ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2)
      (Set.Icc 0 (T : ℝ) ×ˢ Set.univ))
    (θ : (ℝ≥0 → Sandpile.Continuum.Space d) → ℝ≥0)
    (hθm : Measurable θ) (hθT : ∀ p, θ p ≤ T) :
    (∫ ω, G ((T : ℝ) - (θ (fun t => B₁ t ω) : ℝ))
      (B₁ (θ (fun t => B₁ t ω)) ω) ∂P₁) =
    (∫ ω, G ((T : ℝ) - (θ (fun t => B₂ t ω) : ℝ))
      (B₂ (θ (fun t => B₂ t ω)) ω) ∂P₂) := by
  let C := C(ℝ≥0, Sandpile.Continuum.Space d)
  let κ₁ : Ω₁ → C := fun ω => ⟨fun t => B₁ t ω, hBc₁ ω⟩
  let κ₂ : Ω₂ → C := fun ω => ⟨fun t => B₂ t ω, hBc₂ ω⟩
  have hκ₁ : Measurable κ₁ := ContinuousMap.measurable_iff_eval.mpr fun t => (hBm₁ t).measurable
  have hκ₂ : Measurable κ₂ := ContinuousMap.measurable_iff_eval.mpr fun t => (hBm₂ t).measurable
  let τc : C → ℝ≥0 := fun p => θ (fun t => p t)
  have hτcm : Measurable τc := hθm.comp (Measurable.of_eval fun t => ContinuousMap.measurable_eval t)
  have hvalue : Measurable (fun p : C => p (τc p)) :=
    Sandpile.Continuum.measurable_stopped_position
      (fun t => ContinuousMap.measurable_eval t) (fun p => p.continuous) hτcm
  let Gext : ℝ × Sandpile.Continuum.Space d → ℝ :=
    fun p => G (max 0 (min (T : ℝ) p.1)) p.2
  have hGext : Continuous Gext := by
    change Continuous ((fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2) ∘
      fun p : ℝ × Sandpile.Continuum.Space d => (max 0 (min (T : ℝ) p.1), p.2))
    apply hG.comp_continuous
    · exact ((continuous_const.max (continuous_const.min continuous_fst)).prodMk continuous_snd)
    · intro p
      exact ⟨⟨le_max_left _ _, max_le T.coe_nonneg (min_le_left _ _)⟩, Set.mem_univ _⟩
  let R : C → ℝ := fun p => Gext ((T : ℝ) - τc p, p (τc p))
  have hRm : Measurable R := hGext.measurable.comp
    ((measurable_const.sub (measurable_coe_nnreal_real.comp hτcm)).prodMk hvalue)
  have hR : ∀ p, R p = G ((T : ℝ) - τc p) (p (τc p)) := by
    intro p
    dsimp [R, Gext]
    have h0 : (0 : ℝ) ≤ (T : ℝ) - (τc p : ℝ) := sub_nonneg.mpr (by exact_mod_cast hθT (fun t => p t))
    have hT : (T : ℝ) - (τc p : ℝ) ≤ (T : ℝ) := sub_le_self _ (τc p).coe_nonneg
    rw [min_eq_right hT, max_eq_right h0]
  calc
    _ = ∫ ω, R (κ₁ ω) ∂P₁ := by
      apply integral_congr_ae
      exact ae_of_all _ fun ω => (hR (κ₁ ω)).symm
    _ = ∫ p, R p ∂(P₁.map κ₁) := (integral_map_of_stronglyMeasurable hκ₁ hRm.stronglyMeasurable).symm
    _ = ∫ p, R p ∂(P₂.map κ₂) := by rw [hlaw]
    _ = ∫ ω, R (κ₂ ω) ∂P₂ := integral_map_of_stronglyMeasurable hκ₂ hRm.stronglyMeasurable
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ fun ω => hR (κ₂ ω)
