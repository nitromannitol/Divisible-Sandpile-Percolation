import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Diffusive floor-time limits

For two ordered nonnegative observation times, the number of lattice steps
between their floor times has the expected diffusive asymptotics.
-/

open Filter Topology

namespace Sandpile.External.Stopping

/-- Normalized floor-time block lengths converge to the time difference. -/
theorem tendsto_floor_time_block_div_sq (R : ℕ → ℝ) (hR : Tendsto R atTop atTop)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    Tendsto (fun n => ((⌊t * (R n) ^ 2⌋₊ - ⌊s * (R n) ^ 2⌋₊ : ℕ) : ℝ) /
      (R n) ^ 2) atTop (𝓝 (t - s)) := by
  have hR2 : Tendsto (fun n => (R n) ^ 2) atTop atTop := by
    simpa [pow_two] using hR.atTop_mul_atTop₀ hR
  have ht : 0 ≤ t := hs.trans hst
  have htlim := (tendsto_nat_floor_mul_div_atTop ht).comp hR2
  have hslim := (tendsto_nat_floor_mul_div_atTop hs).comp hR2
  have hfloor (n : ℕ) : ⌊s * (R n) ^ 2⌋₊ ≤ ⌊t * (R n) ^ 2⌋₊ :=
    Nat.floor_mono (mul_le_mul_of_nonneg_right hst (sq_nonneg _))
  convert htlim.sub hslim using 1
  funext n
  rw [Nat.cast_sub (hfloor n), sub_div]
  rfl

/-- Positive time intervals contain a diverging number of lattice steps. -/
theorem tendsto_floor_time_block_atTop (R : ℕ → ℝ) (hR : Tendsto R atTop atTop)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s < t) :
    Tendsto (fun n => ⌊t * (R n) ^ 2⌋₊ - ⌊s * (R n) ^ 2⌋₊) atTop atTop := by
  have hR2 : Tendsto (fun n => (R n) ^ 2) atTop atTop := by
    simpa [pow_two] using hR.atTop_mul_atTop₀ hR
  have hratio := tendsto_floor_time_block_div_sq R hR s t hs hst.le
  have hprod := hratio.pos_mul_atTop (sub_pos.mpr hst) hR2
  apply (tendsto_natCast_atTop_iff (R := ℝ)).mp
  apply hprod.congr'
  filter_upwards [hR.eventually_gt_atTop 0] with n hn
  field_simp

/-- The square-root block normalization matches the diffusive spatial scale. -/
theorem tendsto_sqrt_floor_time_block_div (R : ℕ → ℝ) (hR : Tendsto R atTop atTop)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    Tendsto (fun n => Real.sqrt (⌊t * (R n) ^ 2⌋₊ - ⌊s * (R n) ^ 2⌋₊) / R n)
      atTop (𝓝 (Real.sqrt (t - s))) := by
  have h := (tendsto_floor_time_block_div_sq R hR s t hs hst).sqrt
  apply h.congr'
  filter_upwards [hR.eventually_gt_atTop 0] with n hn
  rw [Real.sqrt_div (Nat.cast_nonneg _), Real.sqrt_sq_eq_abs, abs_of_pos hn]
  rw [Nat.cast_sub (Nat.floor_mono (mul_le_mul_of_nonneg_right hst (sq_nonneg _)))]

end Sandpile.External.Stopping
