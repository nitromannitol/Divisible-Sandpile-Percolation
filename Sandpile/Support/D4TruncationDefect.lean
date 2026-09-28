import Sandpile.Support.D4KernelL2

/-!
# The truncation defect between the time-truncated and potential kernels

The defect between the kernel of the time-truncated membrane field and the potential kernel, for
Step 1 of `prop:d4-superdiffusive-limit`. The two kernels differ by the time tail of the heat
kernel at `x` (`green_sub_greenTime`) and a term that does not depend on `x`
(`greenTime_sub_potentialKernel`); the second is annihilated by the `ω`-pairing, whose test
function integrates to zero, so the whole defect is carried by the tail `∑_{j≥t} p_j(x,y)`. The
`α > 2` arithmetic that makes the tail vanish at the superdiffusive times `t_R = ⌊R^α⌋` is
recorded here as well (`tendsto_superdiffusive_defect_scale`), via the equivalence
`R^{1/2}⌊R^α⌋^{-1/4} → 0` (`sandpile.tex:3345-3350`).
-/

open MeasureTheory Filter Topology

namespace Sandpile

variable {d : ℕ}

/-- The tail of the Green series: `G(x,y) - g_t(x,y) = ∑_{j≥t} p_j(x,y)`. -/
theorem green_sub_greenTime (hd : 3 ≤ d) (t : ℕ) (x y : Site d) :
    green d x y - greenTime d t x y = ∑' j : ℕ, heatKernel d (j + t) x y := by
  have hsum : Summable (fun k : ℕ => heatKernel d k x y) :=
    summable_heatKernel_transient hd x y
  have h := hsum.sum_add_tsum_nat_add t
  show (∑' k : ℕ, heatKernel d k x y) - (∑ i ∈ Finset.range t, heatKernel d i x y)
      = ∑' j : ℕ, heatKernel d (j + t) x y
  linarith [h]

/-- The defect between the truncated kernel and the potential kernel is the time
tail at `x` together with a term free of `x`. -/
theorem greenTime_sub_potentialKernel (hd : 3 ≤ d) (t : ℕ) (x y : Site d) :
    greenTime d t x y - potentialKernel d x y =
      green d 0 y - ∑' j : ℕ, heatKernel d (j + t) x y := by
  rw [potentialKernel_eq_green_sub hd, ← green_sub_greenTime hd t x y]
  ring

/-- **The superdiffusive threshold.**  `R^{1/2}⌊R^α⌋^{-1/4} → 0` exactly when
`α > 2`; this is the arithmetic behind the vanishing of the truncation defect at
`t_R = ⌊R^α⌋` (`sandpile.tex:3345-3350`). -/
theorem tendsto_superdiffusive_defect_scale {α : ℝ} (hα : 2 < α) :
    Tendsto (fun R : ℝ => R ^ (2⁻¹ : ℝ) * ((⌊R ^ α⌋₊ : ℝ)) ^ (-(4⁻¹ : ℝ))) atTop (nhds 0) := by
  have hpos : 0 < α / 4 - 2⁻¹ := by linarith
  have hg : Tendsto (fun R : ℝ => (2 : ℝ) ^ (4⁻¹ : ℝ) * R ^ (-(α / 4 - 2⁻¹))) atTop (nhds 0) := by
    simpa using (tendsto_rpow_neg_atTop hpos).const_mul ((2 : ℝ) ^ (4⁻¹ : ℝ))
  refine squeeze_zero' ?_ ?_ hg
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with R hR
    have hR0 : (0 : ℝ) < R := by linarith
    exact mul_nonneg (Real.rpow_nonneg hR0.le _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with R hR
    have hR0 : (0 : ℝ) < R := by linarith
    have hRa : (2 : ℝ) ≤ R ^ α := by
      calc (2 : ℝ) ≤ R := hR
        _ = R ^ (1 : ℝ) := (Real.rpow_one R).symm
        _ ≤ R ^ α := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have hfl : R ^ α / 2 ≤ (⌊R ^ α⌋₊ : ℝ) := by
      have h := Nat.lt_floor_add_one (R ^ α)
      linarith
    have hflpos : (0 : ℝ) < R ^ α / 2 := by linarith
    have hmono : ((⌊R ^ α⌋₊ : ℝ)) ^ (-(4⁻¹ : ℝ)) ≤ (R ^ α / 2) ^ (-(4⁻¹ : ℝ)) := by
      rw [Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_neg hflpos.le]
      exact inv_anti₀ (Real.rpow_pos_of_pos hflpos _)
        (Real.rpow_le_rpow hflpos.le hfl (by norm_num))
    have h1 : (R ^ α / 2) ^ (-(4⁻¹ : ℝ)) = (R ^ α) ^ (-(4⁻¹ : ℝ)) * (2 : ℝ) ^ (4⁻¹ : ℝ) := by
      rw [Real.div_rpow (Real.rpow_nonneg hR0.le α) (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
    have h2 : (R ^ α) ^ (-(4⁻¹ : ℝ)) = R ^ (-(α * 4⁻¹)) := by
      rw [← Real.rpow_mul hR0.le]
      ring_nf
    have key : R ^ (2⁻¹ : ℝ) * (R ^ α / 2) ^ (-(4⁻¹ : ℝ)) =
        (2 : ℝ) ^ (4⁻¹ : ℝ) * R ^ (-(α / 4 - 2⁻¹)) := by
      rw [h1, h2, ← mul_assoc, ← Real.rpow_add hR0, mul_comm]
      congr 2
      ring
    calc R ^ (2⁻¹ : ℝ) * ((⌊R ^ α⌋₊ : ℝ)) ^ (-(4⁻¹ : ℝ))
        ≤ R ^ (2⁻¹ : ℝ) * (R ^ α / 2) ^ (-(4⁻¹ : ℝ)) :=
          mul_le_mul_of_nonneg_left hmono (Real.rpow_nonneg hR0.le _)
      _ = (2 : ℝ) ^ (4⁻¹ : ℝ) * R ^ (-(α / 4 - 2⁻¹)) := key

end Sandpile
