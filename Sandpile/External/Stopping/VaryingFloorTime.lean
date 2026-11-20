import Sandpile.External.Stopping.FloorTimeLimits

/-!
# Diffusive floor times for varying horizons

A vanishing grid size preserves convergence of nonnegative horizons when the
horizons themselves depend on the scale.
-/

open Filter Topology

namespace Sandpile.External.Stopping

/-- Diffusive rounding preserves the limit of a converging sequence of
nonnegative horizons. -/
theorem tendsto_varying_floor_time_div_sq (R T : ℕ → ℝ)
    (hR : Tendsto R atTop atTop) (hT0 : ∀ n, 0 ≤ T n)
    {t : ℝ} (hT : Tendsto T atTop (𝓝 t)) :
    Tendsto (fun n => (⌊R n ^ 2 * T n⌋₊ : ℝ) / R n ^ 2) atTop (𝓝 t) := by
  have hR2 : Tendsto (fun n => R n ^ 2) atTop atTop := by
    simpa [pow_two] using hR.atTop_mul_atTop₀ hR
  have hinv : Tendsto (fun n => 1 / R n ^ 2) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hR2
  have hlower := hT.sub hinv
  have hupper := hT
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using hlower) hupper ?_ ?_
  · filter_upwards [hR.eventually_gt_atTop 0] with n hn
    have hp : 0 < R n ^ 2 := sq_pos_of_pos hn
    have hf := Nat.lt_floor_add_one (R n ^ 2 * T n)
    rw [le_div_iff₀ hp]
    have hi : (1 / R n ^ 2) * R n ^ 2 = 1 := by field_simp
    simp only [one_div] at hi
    nlinarith
  · filter_upwards [hR.eventually_gt_atTop 0] with n hn
    have hp : 0 < R n ^ 2 := sq_pos_of_pos hn
    have hf := Nat.floor_le (mul_nonneg hp.le (hT0 n))
    rw [div_le_iff₀ hp]
    nlinarith

end Sandpile.External.Stopping
