import Mathlib

/-!
# A power bound for the logarithmic singularity

The positive part of the logarithm of an inverse distance is bounded by every
negative power of that distance. This converts local logarithmic covariance
estimates into Riesz estimates.
-/

namespace Sandpile.Support

/-- The positive logarithm of an inverse distance is bounded by a negative
power of the distance, for every positive exponent. -/
theorem log_inv_pos_part_le_rpow {r β : ℝ} (hr : 0 < r) (hβ : 0 < β) :
    max 0 (Real.log r⁻¹) ≤ β⁻¹ * r ^ (-β) := by
  have hp : 0 ≤ β⁻¹ * r ^ (-β) := by positivity
  apply max_le hp
  have he : Real.exp (β * Real.log r⁻¹) = r ^ (-β) := by
    rw [Real.rpow_def_of_pos hr, Real.log_inv]
    congr 1
    ring
  have h := Real.add_one_le_exp (β * Real.log r⁻¹)
  rw [he] at h
  have h' : β * Real.log r⁻¹ ≤ r ^ (-β) := by linarith
  have := mul_le_mul_of_nonneg_left h' (inv_nonneg.mpr hβ.le)
  simpa only [← mul_assoc, inv_mul_cancel₀ hβ.ne', one_mul] using this

end Sandpile.Support
