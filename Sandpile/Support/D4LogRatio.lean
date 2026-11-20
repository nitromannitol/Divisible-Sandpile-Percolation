import Sandpile.Support.D4LogPower

/-!
# Logarithmic ratios and distance bounds

A positive ratio bounded above and below by a squared distance has at most a
logarithmic singularity as that distance vanishes.
-/

namespace Sandpile.Support

/-- Bounds on a positive ratio imply a logarithmic distance bound. -/
theorem abs_log_le_of_sq_div_le {q r c C : ℝ} (hr : 0 < r) (hc : 1 ≤ c)
    (hC : 1 ≤ C) (hlower : r ^ 2 / c ≤ q) (hupper : q ≤ C) :
    |Real.log q| ≤ Real.log C + Real.log c + 2 * max 0 (Real.log r⁻¹) := by
  have hc0 : 0 < c := by linarith
  have hq : 0 < q := lt_of_lt_of_le (div_pos (sq_pos_of_pos hr) hc0) hlower
  have hl := Real.log_le_log (div_pos (sq_pos_of_pos hr) hc0) hlower
  have hu := Real.log_le_log hq hupper
  rw [Real.log_div (pow_ne_zero 2 hr.ne') hc0.ne', Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hcl : 0 ≤ Real.log c := Real.log_nonneg hc
  have hCl : 0 ≤ Real.log C := Real.log_nonneg hC
  have hp : 0 ≤ max 0 (Real.log r⁻¹) := le_max_left _ _
  have hp' : -Real.log r ≤ max 0 (Real.log r⁻¹) := by
    rw [← Real.log_inv]
    exact le_max_right _ _
  apply abs_le.mpr
  constructor <;> linarith

end Sandpile.Support
