import Sandpile.Support.SquareSummableStability

/-!
# Extended nonnegative sums and square-summable defects

The squared `ℓ²` norm of a real coefficient family equals the extended
nonnegative sum of its squared coordinates. Convergence of this sum to zero
therefore implies convergence of the `ℓ²` norm to zero. The extended sum retains
its value at infinity and so does not assign a finite value to a divergent
nonnegative series.
-/

open Filter Topology
open scoped lp ENNReal

namespace Sandpile.Support

/-- The extended sum of squared coordinates of an `ℓ²` vector is its squared
norm. -/
theorem tsum_ofReal_sq_eq_ofReal_norm_sq {ι : Type*} (v : ℓ²(ι, ℝ)) :
    (∑' i, ENNReal.ofReal (v i ^ 2)) = ENNReal.ofReal (‖v‖ ^ 2) := by
  have hv : Summable (fun i => v i ^ 2) := by
    have h := (lp.memℓp v).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    simpa only [ENNReal.toReal_ofNat, Real.norm_eq_abs, Real.rpow_two, sq_abs] using h
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) hv]
  congr 1
  have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) v
  simpa only [ENNReal.toReal_ofNat, Real.norm_eq_abs, Real.rpow_two, sq_abs] using h.symm

/-- Convergence to zero of the extended sum of the squared coordinates implies
convergence of the `ℓ²` norm to zero. -/
theorem tendsto_norm_zero_of_tsum_ofReal_sq_tendsto_zero {α ι : Type*}
    (l : Filter α) (v : α → ℓ²(ι, ℝ))
    (h : Tendsto (fun j => ∑' i, ENNReal.ofReal (v j i ^ 2)) l (𝓝 0)) :
    Tendsto (fun j => ‖v j‖) l (𝓝 0) := by
  have hs : Tendsto (fun j => ‖v j‖ ^ 2) l (𝓝 0) := by
    have ht := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
    simpa only [tsum_ofReal_sq_eq_ofReal_norm_sq, ENNReal.toReal_ofReal (sq_nonneg _),
      ENNReal.toReal_zero, Function.comp_def] using ht
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero, Function.comp_def] using ht

end Sandpile.Support
