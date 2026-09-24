/-
The scale separation of `eq:d4-superdiffusive-scale-separation` against the
SECOND moment the repository proves (`sandpile.tex:3334-3338`).

Step 2 needs `R^2V_R/n_R\to0` with `V_R` the uniform second moment of the
linearization error.  The paper quotes `V_R = C(1+\log\log t_R)`;
`Sandpile.exists_linearization_second_moment_four` proves the cruder
`(1+\log\log t_R)^2+M`, whose square of a logarithm still vanishes against
`n_R\asymp R^{1+\alpha/2}` because `\alpha>2`.  The proof is the first limit of
`eq:d4-superdiffusive-scale-separation` with the squared affine-logarithm
majorant in place of the affine one.
-/
import Sandpile.Support.D4ScaleSepLimits

open Filter Topology

namespace Sandpile.D4Super

/-- The ratio `R^2/n_R` is at most `4R^{-(\alpha/2-1)}` for `R \geq 2`. -/
theorem scale_sep_ratio_bound (α : ℝ) (hα : 2 < α) (R : ℝ) (hR : 2 ≤ R) :
    R ^ 2 / (⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ : ℝ) ≤ 4 / R ^ (α / 2 - 1) := by
  obtain ⟨h0, -⟩ := loglog_floor_rpow_bounds α hα R hR
  have hB : (0:ℝ) < 1 + Real.log (Real.log (⌊R ^ α⌋₊ : ℝ)) := by linarith
  have hb := scale_sep_first_bound α hα R hR
  have hL : R ^ 2 * (1 + Real.log (Real.log (⌊R ^ α⌋₊ : ℝ)))
      / (⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ : ℝ)
      = (R ^ 2 / (⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ : ℝ)) *
        (1 + Real.log (Real.log (⌊R ^ α⌋₊ : ℝ))) := by
    rw [div_mul_eq_mul_div, mul_comm (R ^ 2)]
  have hRgt : 4 * (1 + Real.log (Real.log (⌊R ^ α⌋₊ : ℝ))) / R ^ (α / 2 - 1)
      = (4 / R ^ (α / 2 - 1)) * (1 + Real.log (Real.log (⌊R ^ α⌋₊ : ℝ))) := by
    rw [div_mul_eq_mul_div]
  rw [hL, hRgt] at hb
  exact le_of_mul_le_mul_right hb hB

/-- **The first limit of `eq:d4-superdiffusive-scale-separation`, at the squared
second moment.** -/
theorem tendsto_scale_sep_first_sq (α : ℝ) (hα : 2 < α) (M : ℝ) (hM : 0 ≤ M) :
    Tendsto (fun R : ℝ => R ^ 2 * ((1 + Real.log (Real.log (⌊R ^ α⌋₊ : ℝ))) ^ 2 + M)
        / (⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ : ℝ)) atTop (𝓝 0) := by
  have hc : 0 < α / 2 - 1 := by linarith
  have hmaj : Tendsto (fun R : ℝ =>
      4 * (((1 + Real.sqrt M) + α * Real.log R) ^ 2 / R ^ (α / 2 - 1))) atTop (𝓝 0) := by
    simpa using (tendsto_sq_affine_log_div_rpow α (1 + Real.sqrt M) (α / 2 - 1) hc).const_mul 4
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with R hR
    positivity
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with R hR
    obtain ⟨h0, hle⟩ := loglog_floor_rpow_bounds α hα R hR
    have hR0 : (0:ℝ) < R := by linarith
    have hlogR : 0 ≤ Real.log R := Real.log_nonneg (by linarith)
    have hD : (0:ℝ) < R ^ (α / 2 - 1) := Real.rpow_pos_of_pos hR0 _
    have hV0 : (0:ℝ) ≤ (1 + Real.log (Real.log (⌊R ^ α⌋₊ : ℝ))) ^ 2 + M := by positivity
    have hratio := scale_sep_ratio_bound α hα R hR
    have hsplit : R ^ 2 * ((1 + Real.log (Real.log (⌊R ^ α⌋₊ : ℝ))) ^ 2 + M)
        / (⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ : ℝ)
        = (R ^ 2 / (⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ : ℝ)) *
          ((1 + Real.log (Real.log (⌊R ^ α⌋₊ : ℝ))) ^ 2 + M) := by
      rw [div_mul_eq_mul_div, mul_comm (R ^ 2)]
    have hsq : (1 + Real.log (Real.log (⌊R ^ α⌋₊ : ℝ))) ^ 2 + M ≤
        ((1 + Real.sqrt M) + α * Real.log R) ^ 2 := by
      have h1 : 1 + Real.log (Real.log (⌊R ^ α⌋₊ : ℝ)) ≤ 1 + α * Real.log R := by linarith
      have h2 : (0:ℝ) ≤ 1 + Real.log (Real.log (⌊R ^ α⌋₊ : ℝ)) := by linarith
      have h3 : (1 + Real.log (Real.log (⌊R ^ α⌋₊ : ℝ))) ^ 2 ≤ (1 + α * Real.log R) ^ 2 :=
        pow_le_pow_left₀ h2 h1 2
      have hMs : Real.sqrt M ^ 2 = M := Real.sq_sqrt hM
      have hMs0 : (0:ℝ) ≤ Real.sqrt M := Real.sqrt_nonneg M
      have hax : (0:ℝ) ≤ 1 + α * Real.log R := by nlinarith
      nlinarith [h3, hMs, hMs0, hax]
    calc R ^ 2 * ((1 + Real.log (Real.log (⌊R ^ α⌋₊ : ℝ))) ^ 2 + M)
          / (⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ : ℝ)
        = (R ^ 2 / (⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ : ℝ)) *
            ((1 + Real.log (Real.log (⌊R ^ α⌋₊ : ℝ))) ^ 2 + M) := hsplit
      _ ≤ (4 / R ^ (α / 2 - 1)) *
            ((1 + Real.log (Real.log (⌊R ^ α⌋₊ : ℝ))) ^ 2 + M) :=
          mul_le_mul_of_nonneg_right hratio hV0
      _ ≤ (4 / R ^ (α / 2 - 1)) * ((1 + Real.sqrt M) + α * Real.log R) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = 4 * (((1 + Real.sqrt M) + α * Real.log R) ^ 2 / R ^ (α / 2 - 1)) := by ring

end Sandpile.D4Super
