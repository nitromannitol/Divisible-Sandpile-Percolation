import Sandpile.Support.D4SpectralLimit
import Sandpile.Support.D4DefectOmega

/-!
# The four-dimensional `ω`-covariance

The `ω`-representative applies the membrane covariance to shifted test
functions. Its variance scales linearly with the scenery variance, and its
unit-variance diagonal is nonnegative by the spectral-energy representation.
-/

open MeasureTheory

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

/-- The `ω`-covariance is the membrane covariance of the shifted tests. -/
theorem omegaMembraneCov4_eq_membraneCov4 (D : Set (Space 4)) (w : Space 4 → ℝ)
    (q : ℝ) (φ ψ : Space 4 → ℝ) :
    Sandpile.omegaMembraneCov4 D w q φ ψ =
      membraneCov4 q (omegaShift D w φ) (omegaShift D w ψ) := rfl

/-- The membrane covariance is linear in the scenery variance. -/
theorem membraneCov4_eq_mul_one (q : ℝ) (φ ψ : Space 4 → ℝ) :
    membraneCov4 q φ ψ = q * membraneCov4 1 φ ψ := by
  unfold membraneCov4
  ring

/-- The unit-variance membrane covariance is nonnegative on the diagonal. -/
theorem membraneCov4_one_self_nonneg (ψ : Space 4 → ℝ) : 0 ≤ membraneCov4 1 ψ ψ := by
  rw [membraneCov4_one_eq_spectralEnergy]
  exact integral_nonneg fun ξ => by unfold membraneSpectralEnergy; positivity

/-- The `ω`-covariance is the scenery variance times the unit-variance
covariance of the shifted test. -/
theorem omegaMembraneCov4_self_eq_mul (D : Set (Space 4)) (w φ : Space 4 → ℝ) (q : ℝ) :
    Sandpile.omegaMembraneCov4 D w q φ φ =
      q * membraneCov4 1 (omegaShift D w φ) (omegaShift D w φ) := by
  rw [omegaMembraneCov4_eq_membraneCov4, membraneCov4_eq_mul_one]

end Sandpile.Support
