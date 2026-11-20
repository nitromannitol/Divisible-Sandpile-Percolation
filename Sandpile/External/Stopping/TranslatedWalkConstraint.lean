import Sandpile.External.Stopping.TranslatedCubeConstraint
import Sandpile.External.Stopping.CubeInterpolationConstraint

/-!
# Translated cube constraints for killed walks

An interpolated killed walk remains close to the unit cube centered at the
limiting rescaled starting point before its stopping time.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- A killed interpolated walk lies within one mesh step and the center error
of the unit cube about a prescribed point. -/
theorem ae_diffusiveWalkPath_translated_cube_constraint
    {d : ℕ} [NeZero d] {R : ℝ} (hR : 0 < R) (q : Site d)
    (a : Continuum.Space d) (θ : (ℕ → Site d) → ℝ≥0)
    (hkill : ∀ᵐ X ∂(walkLaw d q), ∀ j : ℕ,
      (j : ℝ) < R ^ 2 * (θ X : ℝ) → X j ∈ supBox q R) :
    ∀ᵐ X ∂(walkLaw d q), (diffusiveWalkPath R X, θ X) ∈
      translatedCubeConstrainedPaths a (1 + 1 / R + ‖Lclt.scaledSite R q - a‖) := by
  filter_upwards [ae_centeredWalkPath_cube_constraint hR q θ hkill] with X hX
  intro t ht i
  have hc : |(Lclt.scaledSite R q - a) i| ≤ ‖Lclt.scaledSite R q - a‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (Lclt.scaledSite R q - a) i
  have heq : diffusiveWalkPath R X t i - a i =
      centeredWalkPath R q X t i + (Lclt.scaledSite R q - a) i := by
    change diffusiveWalk R t X i - a i =
      (diffusiveWalk R t X - Lclt.scaledSite R q) i + (Lclt.scaledSite R q - a) i
    simp only [PiLp.sub_apply]
    ring
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add (hX t ht i) hc)

end Sandpile.External.Stopping
