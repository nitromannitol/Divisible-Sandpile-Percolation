/-
The vanishing of the error bound in the summed profile of Step 2 of
`thm:dgt4-many-limits` (`sandpile.tex:6245-6250`): with `R_k → ∞`, `L_k → ∞` and
`η_k → 0`, the bound `C/L_k + 1/(κR_k²) + Tη_k/κ` tends to `0`.
-/
import Mathlib

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile.Support

/-- The error bound of the summed profile tends to zero. -/
theorem tendsto_bound_of_scaled
    (R L η : ℕ → ℝ) (C κ G00 T : ℝ) (hκ : 0 < κ)
    (hR : Tendsto R atTop atTop) (hL : Tendsto L atTop atTop)
    (hη : Tendsto η atTop (𝓝 0)) :
    Tendsto (fun k : ℕ => C / L k + 1 / (κ * R k ^ 2) + η k * G00 * T) atTop (𝓝 0) := by
  have h1 : Tendsto (fun k : ℕ => C / L k) atTop (𝓝 0) := hL.const_div_atTop C
  have h2 : Tendsto (fun k : ℕ => 1 / (κ * R k ^ 2)) atTop (𝓝 0) := by
    have hR2 : Tendsto (fun k : ℕ => R k ^ 2) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0)).comp hR
    exact (hR2.const_mul_atTop hκ).const_div_atTop 1
  have h3 : Tendsto (fun k : ℕ => η k * G00 * T) atTop (𝓝 0) := by
    have h4 : Tendsto (fun k : ℕ => η k * G00) atTop (𝓝 (0 * G00)) := hη.mul tendsto_const_nhds
    have h5 : Tendsto (fun k : ℕ => η k * G00 * T) atTop (𝓝 (0 * G00 * T)) :=
      h4.mul tendsto_const_nhds
    simpa using h5
  simpa using (h1.add h2).add h3

/-- The vanishing of the pointwise bound when the summation starts at an
offset `s_k` with `s_k = o(R_k^2)`. -/
theorem tendsto_bound_of_scaled_offset
    (R L η : ℕ → ℝ) (s : ℕ → ℕ) (C κ G00 T : ℝ) (hκ : 0 < κ)
    (hR : Tendsto R atTop atTop) (hL : Tendsto L atTop atTop)
    (hη : Tendsto η atTop (𝓝 0))
    (hs : Tendsto (fun k : ℕ => ((s k : ℕ) : ℝ) / R k ^ 2) atTop (𝓝 0)) :
    Tendsto (fun k : ℕ => C / L k + (1 + ((s k : ℕ) : ℝ)) / (κ * R k ^ 2) + η k * G00 * T)
      atTop (𝓝 0) := by
  have h1 : Tendsto (fun k : ℕ => C / L k) atTop (𝓝 0) := hL.const_div_atTop C
  have hR2 : Tendsto (fun k : ℕ => R k ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hR
  have h2 : Tendsto (fun k : ℕ => 1 / (κ * R k ^ 2)) atTop (𝓝 0) :=
    (hR2.const_mul_atTop hκ).const_div_atTop 1
  have h2' : Tendsto (fun k : ℕ => 1 / κ * (((s k : ℕ) : ℝ) / R k ^ 2)) atTop (𝓝 0) := by
    simpa using hs.const_mul (1 / κ)
  have h3 : Tendsto (fun k : ℕ => η k * G00 * T) atTop (𝓝 0) := by
    simpa using (hη.mul_const G00).mul_const T
  have hsum := (h1.add (h2.add h2')).add h3
  rw [show (0 : ℝ) + (0 + 0) + 0 = 0 by ring] at hsum
  refine Tendsto.congr' ?_ hsum
  filter_upwards [hR.eventually_gt_atTop 0] with k hk
  have hRne : R k ≠ 0 := ne_of_gt hk
  have hκne : κ ≠ 0 := ne_of_gt hκ
  field_simp

end Sandpile.Support
