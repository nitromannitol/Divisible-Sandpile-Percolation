import Sandpile.External.Stopping.KilledRewardApproximation

/-!
# Temporal continuity of spatially localized rewards

A continuous reward supported in a fixed compact set of spatial points has a
uniform temporal modulus on every bounded time interval. This supplies the
rounding estimate for spatially localized rewards.
-/

open Filter Set
open scoped Topology

namespace Sandpile.External.Stopping

/-- A continuous reward supported in a common compact spatial set is uniformly
continuous in time, uniformly over all spatial points and a compact interval. -/
theorem exists_uniform_temporal_modulus_of_compact_support
    {E : Type*} [MetricSpace E] (K : Set E) (hK : IsCompact K) (T : ℝ)
    (G : ℝ → E → ℝ) (hG : Continuous (fun p : ℝ × E => G p.1 p.2))
    (hsupp : ∀ s z, z ∉ K → G s z = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s ∈ Icc (0 : ℝ) T, ∀ u ∈ Icc (0 : ℝ) T, ∀ z,
      |s - u| < δ → |G s z - G u z| ≤ ε := by
  have hu : UniformContinuousOn (fun p : ℝ × E => G p.1 p.2) (Icc (0 : ℝ) T ×ˢ K) :=
    (isCompact_Icc.prod hK).uniformContinuousOn_of_continuous hG.continuousOn
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  refine ⟨δ, hδ, ?_⟩
  intro s hs u hu z hsu
  by_cases hz : z ∈ K
  · have hdist : dist (s, z) (u, z) < δ := by
      simpa only [Prod.dist_eq, dist_self, max_lt_iff, Real.dist_eq] using ⟨hsu, hδ⟩
    have h := hmod (s, z) ⟨hs, hz⟩ (u, z) ⟨hu, hz⟩ hdist
    exact le_of_lt (by simpa only [Real.dist_eq] using h)
  · simp [hsupp s z hz, hsupp u z hz, hε.le]

/-- The temporal modulus of a compactly supported continuous reward controls
one diffusive grid step uniformly at all sufficiently large scales. -/
theorem exists_large_scale_uniform_temporal_modulus_of_compact_support
    {E : Type*} [MetricSpace E] (K : Set E) (hK : IsCompact K) (T : ℝ)
    (G : ℝ → E → ℝ) (hG : Continuous (fun p : ℝ × E => G p.1 p.2))
    (hsupp : ∀ s z, z ∉ K → G s z = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ R₀ > 0, ∀ R ≥ R₀, ∀ s ∈ Icc (0 : ℝ) T, ∀ u ∈ Icc (0 : ℝ) T, ∀ z,
      |s - u| < 1 / R ^ 2 → |G s z - G u z| ≤ ε := by
  obtain ⟨δ, hδ, hmod⟩ :=
    exists_uniform_temporal_modulus_of_compact_support K hK T G hG hsupp hε
  have ht : Tendsto (fun R : ℝ => 1 / R ^ 2) atTop (𝓝 0) := by
    simpa only [one_div, inv_pow, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      ((tendsto_inv_atTop_zero : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0)).pow 2)
  have hevent : ∀ᶠ R : ℝ in atTop, 1 / R ^ 2 < δ := ht.eventually (Iio_mem_nhds hδ)
  obtain ⟨a, ha⟩ := eventually_atTop.mp hevent
  refine ⟨max a 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro R hR s hs u hu z hsu
  apply hmod s hs u hu z
  exact hsu.trans (ha R (le_trans (le_max_left _ _) hR))

end Sandpile.External.Stopping
