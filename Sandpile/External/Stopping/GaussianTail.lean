import Sandpile.External.Stopping.WalkModulusGaussian

/-!
# Gaussian tails and finite-grid counts

The exponential decay in a Gaussian modulus estimate dominates the linear
growth of the number of grid intervals.
-/

open Filter Topology

namespace Sandpile.External.Stopping

/-- An exponential tail dominates a linear grid-count factor. -/
theorem tendsto_linear_mul_exp_neg_mul (L C a : ℝ) (ha : 0 < a) :
    Tendsto (fun u : ℝ => (L * u + 1) * C * Real.exp (-a * u)) atTop (𝓝 0) := by
  have hlinear : Tendsto (fun u : ℝ => u * Real.exp (-a * u)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 a ha
  have hexp : Tendsto (fun u : ℝ => Real.exp (-a * u)) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop ha)
    simpa only [Function.comp_def, id_eq, neg_mul] using h
  have h := (hlinear.const_mul L).add hexp
  have h' := h.mul_const C
  convert h' using 1
  · ext u
    ring
  · simp

end Sandpile.External.Stopping
