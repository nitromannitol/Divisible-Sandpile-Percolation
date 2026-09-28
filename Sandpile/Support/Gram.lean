import Sandpile.External.BerryEsseen

/-!
# The covariance matrix of the linear forms is positive semidefinite

The covariance matrix of the linear forms of `thm:critical-toppling` is positive semidefinite.

`Sandpile.External.BerryEsseen.gram ν a` is `Var(ν)` times the Gram matrix of the coefficient
family `a`, so it is symmetric and its quadratic form is a nonnegative multiple of a sum of
squares. This is what lets the persistence bound for the multivariate Gaussian, which is stated
for a covariance matrix, be applied to it: the matrix fed to `multivariateGaussian` in
`Sandpile.External.MultivariateBerryEsseen` is never an arbitrary matrix.
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace Sandpile.External.BerryEsseen

/-- The covariance matrix of the linear forms is `Var(ν)` times a Gram matrix. -/
theorem gram_eq_smul_gram {N m : ℕ} (ν : Measure ℝ) (a : Fin N → Fin m → ℝ) :
    gram ν a = variance id ν • ((Matrix.of a)ᴴ * Matrix.of a) := by
  ext j k
  simp [gram, Matrix.mul_apply]

/-- **The covariance matrix is positive semidefinite.** -/
theorem gram_posSemidef {N m : ℕ} (ν : Measure ℝ) (a : Fin N → Fin m → ℝ) :
    (gram ν a).PosSemidef := by
  rw [gram_eq_smul_gram]
  exact (Matrix.posSemidef_conjTranspose_mul_self _).smul (variance_nonneg _ _)

end Sandpile.External.BerryEsseen
