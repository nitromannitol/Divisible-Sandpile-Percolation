import Sandpile.External.Stopping.CompactRewardModulus
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Spatial translations of localized rewards

A continuous reward with compact spatial support is uniformly continuous
under small spatial translations on every compact time interval.
-/

open Filter Set
open scoped Topology

namespace Sandpile.External.Stopping

/-- Small translations change a compactly supported reward uniformly over
spatial points and a bounded time interval. -/
theorem exists_uniform_spatial_translation_of_compact_support
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    (K : Set E) (hK : IsCompact K) (T : ℝ)
    (G : ℝ → E → ℝ) (hG : Continuous (fun p : ℝ × E => G p.1 p.2))
    (hsupp : ∀ s z, z ∉ K → G s z = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s ∈ Icc (0 : ℝ) T, ∀ z v, ‖v‖ < δ →
      |G s (z + v) - G s z| ≤ ε := by
  let L := Metric.cthickening 1 K
  have hL : IsCompact L := hK.cthickening
  have hKL : K ⊆ L := by
    intro z hz
    apply Metric.thickening_subset_cthickening 1 K
    exact Metric.mem_thickening_iff.mpr ⟨z, hz, by simp⟩
  have hu : UniformContinuousOn (fun p : ℝ × E => G p.1 p.2) (Icc (0 : ℝ) T ×ˢ L) :=
    (isCompact_Icc.prod hL).uniformContinuousOn_of_continuous hG.continuousOn
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  refine ⟨min δ 1, lt_min hδ zero_lt_one, ?_⟩
  intro s hs z v hv
  have hvδ : ‖v‖ < δ := hv.trans_le (min_le_left _ _)
  have hv1 : ‖v‖ < 1 := hv.trans_le (min_le_right _ _)
  by_cases hz : z ∈ K
  · have hzv : z + v ∈ L := by
      apply Metric.thickening_subset_cthickening 1 K
      apply Metric.mem_thickening_iff.mpr
      refine ⟨z, hz, ?_⟩
      simpa only [dist_eq_norm, add_sub_cancel_left] using hv1
    have hd : dist (s, z + v) (s, z) < δ := by
      rw [Prod.dist_eq, dist_self, show dist (z + v) z = ‖v‖ by
        simp only [dist_eq_norm, add_sub_cancel_left], max_eq_right (norm_nonneg v)]
      exact hvδ
    have h := hmod (s, z + v) ⟨hs, hzv⟩ (s, z) ⟨hs, hKL hz⟩ hd
    exact le_of_lt (by simpa only [Real.dist_eq] using h)
  · by_cases hzv : z + v ∈ K
    · have hzL : z ∈ L := by
        apply Metric.thickening_subset_cthickening 1 K
        apply Metric.mem_thickening_iff.mpr
        refine ⟨z + v, hzv, ?_⟩
        simpa only [dist_eq_norm, sub_add_cancel_left, norm_neg] using hv1
      have hd : dist (s, z + v) (s, z) < δ := by
        rw [Prod.dist_eq, dist_self, show dist (z + v) z = ‖v‖ by
          simp only [dist_eq_norm, add_sub_cancel_left], max_eq_right (norm_nonneg v)]
        exact hvδ
      have h := hmod (s, z + v) ⟨hs, hKL hzv⟩ (s, z) ⟨hs, hzL⟩ hd
      exact le_of_lt (by simpa only [Real.dist_eq] using h)
    · simp only [hsupp s z hz, hsupp s (z + v) hzv, sub_self, abs_zero, hε.le]

end Sandpile.External.Stopping
