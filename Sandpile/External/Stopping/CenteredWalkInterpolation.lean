import Sandpile.External.Stopping.LatticeCubeClockLimit
import Sandpile.External.Stopping.WalkContinuity

/-!
# Centered diffusive walk interpolation

The graph interpolation of centered, rescaled lattice sites is the centered
version of the diffusively rescaled walk used in the invariance principle.
-/

open scoped NNReal

namespace Sandpile.External.Stopping

/-- Centering the walk before or after diffusive interpolation gives the same
continuous path. -/
theorem centered_constantStep_path_eq_diffusiveWalk {d : ℕ} (R : ℝ) (q : Site d)
    (X : ℕ → Site d) (t : ℝ≥0) :
    LatticeProb.ConstantStepInterpolation.path (R ^ 2) (centeredScaledSite R q ∘ X) t =
      diffusiveWalk R t X - Lclt.scaledSite R q := by
  have ht : ((⟨R ^ 2, sq_nonneg R⟩ * t : ℝ≥0) : ℝ) = R ^ 2 * (t : ℝ) := by
    rfl
  unfold diffusiveWalk linearWalk
  rw [ht]
  ext i
  simp only [LatticeProb.ConstantStepInterpolation.path, Function.comp_apply,
    AffineMap.lineMap_apply_module, centeredScaledSite, Lclt.scaledSite,
    PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, Pi.sub_apply, Int.cast_sub]
  ring

end Sandpile.External.Stopping
