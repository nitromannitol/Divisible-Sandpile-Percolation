import Sandpile.External.RSW.AspectReduction
import Sandpile.External.RSW.FiniteScales
import Sandpile.External.RSW.HomeomorphismProduct
import Sandpile.External.RSW.ScaledInterpolation

/-!
# Reduction to large geometric scales

A universal aspect-eight comparison on a geometric sequence starting at any positive
integer base implies the full planar RSW comparison. Bounded scales are handled by
one-site association estimates.
-/

open MeasureTheory Set

namespace Sandpile.External.RSW

/-- The universal aspect-eight comparison at geometric scales with base `M`. -/
def PlanarRSWAspectEightBaseFour (M : ℕ) : Prop :=
  ∃ ψ : Icc (0 : ℝ) 1 ≃o Icc (0 : ℝ) 1,
    ∀ μ : Measure (Site 2 → ℝ), ∀ [IsProbabilityMeasure μ],
      IsSymmetricPlanarLaw μ → IsAssociatedPlanarLaw μ →
      ∀ j : ℕ, ∀ level : ℝ,
        (ψ (probabilityInUnitInterval μ
          (planarCrossingEvent (2 * (M * 4 ^ j)) (16 * (M * 4 ^ j)) level)) : ℝ) ≤
          μ.real (planarCrossingEvent (16 * (M * 4 ^ j)) (2 * (M * 4 ^ j)) level)

/-- A universal aspect-eight comparison on base-four scales above any positive base
implies the full planar crossing comparison. -/
theorem planarRSW_of_aspect_eight_base_four {M : ℕ} (hM : 0 < M)
    (h : PlanarRSWAspectEightBaseFour M) : Sandpile.External.PlanarRSW := by
  obtain ⟨ψ, hψ⟩ := h
  obtain ⟨χ, hχ⟩ := bounded_scale_crossing_comparison M
  apply planarRSW_of_aspect_two
  refine ⟨unitIntervalIsoProduct ψ χ, ?_⟩
  intro μ _ hsym hass n hn level
  by_cases hsmall : n ≤ M
  · exact (show (unitIntervalIsoProduct ψ χ
        (probabilityInUnitInterval μ (planarCrossingEvent (2 * n) (4 * n) level)) : ℝ) ≤
      (χ (probabilityInUnitInterval μ (planarCrossingEvent (2 * n) (4 * n) level)) : ℝ)
        from unitIntervalIsoProduct_le_right ψ χ _).trans (hχ μ hsym hass n hsmall level)
  · have hlarge := crossing_comparison_two_of_eight_base_four μ ψ hM
      (show M ≤ n by omega) level (fun j => hψ μ hsym hass j level)
    exact (show (unitIntervalIsoProduct ψ χ
        (probabilityInUnitInterval μ (planarCrossingEvent (2 * n) (4 * n) level)) : ℝ) ≤
      (ψ (probabilityInUnitInterval μ (planarCrossingEvent (2 * n) (4 * n) level)) : ℝ)
        from unitIntervalIsoProduct_le_left ψ χ _).trans hlarge

end Sandpile.External.RSW
