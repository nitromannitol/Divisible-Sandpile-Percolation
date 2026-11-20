import Sandpile.Support.ShiftedBrownianRewardBound
import Sandpile.Support.D23CubeValueRegularity
import Mathlib.Topology.Sequences

/-!
# Spatial continuity of stopped rewards

For a fixed bounded stopping rule, the expected reward of a translated
Brownian path varies continuously with its starting point.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- The payoff of a fixed bounded stopping rule is continuous under a spatial
translation of a Brownian path. -/
theorem Sandpile.Support.continuous_integral_translated_stopping_payoff
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (x : Sandpile.Continuum.Space d)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → Sandpile.Continuum.Space d)
    (hB : Sandpile.Continuum.IsBrownian d x B P)
    (hBm : ∀ t, StronglyMeasurable (B t)) (hBc : ∀ ω, Continuous fun t => B t ω)
    (T : ℝ≥0) (G : ℝ → Sandpile.Continuum.Space d → ℝ)
    (hG : ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2)
      (Set.Icc 0 (T : ℝ) ×ˢ Set.univ))
    (hgrow : ∃ C k : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) (T : ℝ),
      ∀ y, |G t y| ≤ C * (1 + ‖y‖) ^ k)
    (τ : Ω → ℝ≥0) (hτ : Sandpile.Continuum.IsBrownianStopping B τ)
    (hτT : ∀ ω, τ ω ≤ T) :
    Continuous fun y : Sandpile.Continuum.Space d =>
      ∫ ω, G ((T : ℝ) - τ ω) (y + B (τ ω) ω) ∂P := by
  have hmeas : ∀ y : Sandpile.Continuum.Space d,
      AEStronglyMeasurable (fun ω => G ((T : ℝ) - τ ω) (y + B (τ ω) ω)) P := by
    intro y
    let C : ℝ≥0 → Ω → Sandpile.Continuum.Space d := fun t ω => y + B t ω
    have hCm : ∀ t, StronglyMeasurable (C t) := fun t =>
      (measurable_const.add (hBm t).measurable).stronglyMeasurable
    have hCc : ∀ ω, Continuous fun t => C t ω := fun ω => continuous_const.add (hBc ω)
    have hτC : Sandpile.Continuum.IsBrownianStopping C τ :=
      (Sandpile.Support.isBrownianStopping_add_const y B τ).mpr hτ
    exact (Sandpile.Support.brownian_stopping_reward_regular P C hCc hCm T G hG).2 τ hτC hτT
  have hGslice : ∀ t ∈ Set.Icc (0 : ℝ) (T : ℝ), Continuous (G t) := by
    intro t ht
    change Continuous ((fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2) ∘ fun y => (t, y))
    exact hG.comp_continuous (continuous_const.prodMk continuous_id) (fun _ => ⟨ht, Set.mem_univ _⟩)
  rw [continuous_iff_seqContinuous]
  intro ys y hy
  let K : Set (Sandpile.Continuum.Space d) := Set.range ys ∪ {y}
  have hK : Bornology.IsBounded K :=
    (Metric.isBounded_range_of_tendsto ys hy).union Bornology.isBounded_singleton
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hK
  let R' : ℝ := max R 0
  have hR' : 0 ≤ R' := le_max_right _ _
  have hKR : ∀ z ∈ K, ‖z‖ ≤ R' := fun z hz => (hR z hz).trans (le_max_left _ _)
  obtain ⟨D, hDi, hD⟩ := Sandpile.Support.exists_integrable_shifted_brownian_reward_bound
    x P B hB hBm hBc T G hgrow K R' hR' hKR
  apply tendsto_integral_of_dominated_convergence D
  · exact fun n => hmeas (ys n)
  · exact hDi
  · intro n
    filter_upwards [hD] with ω hω
    have ht : (T : ℝ) - τ ω ∈ Set.Icc (0 : ℝ) (T : ℝ) :=
      ⟨sub_nonneg.mpr (by exact_mod_cast hτT ω), sub_le_self _ (τ ω).coe_nonneg⟩
    exact hω _ ht (ys n) (Or.inl ⟨n, rfl⟩) _ (hτT ω)
  · exact Eventually.of_forall fun ω => by
      have ht : (T : ℝ) - τ ω ∈ Set.Icc (0 : ℝ) (T : ℝ) :=
        ⟨sub_nonneg.mpr (by exact_mod_cast hτT ω), sub_le_self _ (τ ω).coe_nonneg⟩
      exact ((hGslice _ ht).tendsto (y + B (τ ω) ω)).comp (hy.add tendsto_const_nhds)
