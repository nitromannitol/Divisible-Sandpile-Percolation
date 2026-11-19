import Sandpile.External.RSW.AspectReduction
import Sandpile.External.RSW.ScaleInterpolation

/-!
# Reduction to aspect-eight comparisons on powers of four

The full integer-aspect planar crossing comparison follows from an aspect-eight comparison
at scales that are powers of four.
-/

open MeasureTheory Set

namespace Sandpile.External.RSW

/-- The universal aspect-eight comparison on scales that are powers of four. -/
def PlanarRSWAspectEightPowers : Prop :=
  ∃ ψ : Icc (0 : ℝ) 1 ≃o Icc (0 : ℝ) 1,
    ∀ μ : Measure (Site 2 → ℝ), ∀ [IsProbabilityMeasure μ],
      IsSymmetricPlanarLaw μ → IsAssociatedPlanarLaw μ →
      ∀ j : ℕ, ∀ level : ℝ,
        (ψ (probabilityInUnitInterval μ
          (planarCrossingEvent (2 * 4 ^ j) (16 * 4 ^ j) level)) : ℝ) ≤
          μ.real (planarCrossingEvent (16 * 4 ^ j) (2 * 4 ^ j) level)

/-- Aspect-eight comparisons on powers of four imply the full planar RSW comparison. -/
theorem planarRSW_of_aspect_eight_powers (h : PlanarRSWAspectEightPowers) :
    Sandpile.External.PlanarRSW := by
  obtain ⟨ψ, hψ⟩ := h
  apply planarRSW_of_aspect_two
  refine ⟨ψ, ?_⟩
  intro μ _ hsym hass n hn level
  exact crossing_comparison_two_of_eight_pow_four μ ψ level
    (fun j => hψ μ hsym hass j level) hn

end Sandpile.External.RSW
