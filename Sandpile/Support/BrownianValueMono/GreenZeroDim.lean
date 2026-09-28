import Sandpile.Continuum.Kernel

/-!
# The dimension-zero heat and Green kernels

In dimension `0` the space `Space 0` is a single point, so the Brownian transition density
`heatKernelBM` is identically `1` and the finite-time Green kernel `greenTimeBM` is the identity
function of the time argument. This is the elementary fact behind the samplewise growth residual
`Sandpile.Continuum.ballGrowthResidual_zero` and, here, behind the exact affine structure of the
Gaussian heat potential `Z` in dimension zero.
-/

namespace Sandpile.Continuum

/-- In dimension zero the Brownian heat kernel is identically `1`, for every time. -/
theorem heatKernelBM_zero_dim (t : ℝ) (x y : Space 0) : heatKernelBM 0 t x y = 1 := by
  unfold heatKernelBM
  norm_num

/-- In dimension zero the finite-time Green kernel is the identity function of the time
argument, for every pair of points. -/
theorem greenTimeBM_zero_dim (t : ℝ) (x y : Space 0) : greenTimeBM 0 t x y = t := by
  unfold greenTimeBM
  have h1 : (fun s : ℝ => heatKernelBM 0 s x y) = fun _ => (1 : ℝ) := by
    funext s
    exact heatKernelBM_zero_dim s x y
  rw [h1]
  simp

end Sandpile.Continuum
