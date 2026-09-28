import Sandpile.Support.CrossField

/-!
# Translation symmetry of the ball field

The ball field of `sandpile.tex:2076-2088` and the plane symmetries: the first step of the
symmetry hypothesis the continuum crossing comparison asks for. `𝒳_s(u)` is the white
noise tested against `ballKernel d s u`, the Green function of the ball of radius `s` about
`u`, so the kernel depends on `u` and on the integration variable `z` only through the
vector `planePoint u - z`. Translating the point of the plane is therefore translating the
kernel (`ballKernel_translate`), and since the covariance of the white noise is the `L²`
inner product, which is invariant under a translation of the plane, the translated ball
field has the same finite-dimensional distributions as the ball field. That is
`Sandpile.Continuum.IsSymmetricField` for the translation part; the coordinate interchange
and the sign changes are the same computation for the corresponding change of variables,
and the sign flip of the values is the symmetry of the centred Gaussian law. Those steps
are not written here.
-/

open MeasureTheory Set

namespace Sandpile.Frozen.FixedScaleCrossings

/-- The plane point of a sum is the sum of the plane points. -/
theorem planePoint_add {d : ℕ} (u v : Sandpile.Continuum.Space 2) :
    (planePoint (d := d) (u + v)) = planePoint (d := d) u + planePoint (d := d) v := by
  ext i
  simp only [planePoint, PiLp.add_apply]
  by_cases h : (i : ℕ) < 2
  · simp [h]
  · simp [h]

/-- The ball kernel at a translated point is the translated ball kernel. -/
theorem ballKernel_translate {d : ℕ} (s : ℝ) (u v : Sandpile.Continuum.Space 2)
    (z : Sandpile.Continuum.Space d) :
    ballKernel d s (u + v) z = ballKernel d s u (z - planePoint (d := d) v) := by
  have h : (planePoint (d := d) (u + v)) - z
      = planePoint (d := d) u - (z - planePoint (d := d) v) := by
    rw [planePoint_add]; abel
  unfold ballKernel
  rw [h]

end Sandpile.Frozen.FixedScaleCrossings
