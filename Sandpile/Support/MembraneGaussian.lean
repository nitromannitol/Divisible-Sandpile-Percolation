/-
The Gaussian limit and exact logarithmic variance of the dimension-four membrane
from the paired heat-kernel estimate and the weighted independent-row theorem.
-/
import Sandpile.Support.DoubleHeatKernel
import LatticeProb.Prob.WeightedCLT

open LatticeProb

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile

theorem green_square_eq_double_kernel (d t : ℕ) :
    (∑' y : Site d, greenTime d t 0 y ^ 2) =
      ∑ a ∈ Finset.range t, ∑ b ∈ Finset.range t, heatKernel d (a + b) 0 0 := by
  simp_rw [greenTime_eq_srwGreen]
  rw [LatticeProb.tsum_srwGreen_sq]
  simp only [heatKernel_eq_srwHeat, sub_self]

theorem tendsto_green_square_div_log_four (hPaired : External.PairedLocalCLTFour) :
    Tendsto (fun t : ℕ => (∑' y : Site 4, greenTime 4 t 0 y ^ 2) / Real.log t) atTop
      (𝓝 (4 / Real.pi ^ 2)) := by
  obtain ⟨C, hC⟩ := exists_double_heat_kernel_four_bound hPaired
  have hb (t : ℕ) (ht : 2 ≤ t) :
      |(∑' y : Site 4, greenTime 4 t 0 y ^ 2) - 4 / Real.pi ^ 2 * Real.log t| ≤ C := by
    have h := hC t ht (0 : Site 4) 0 (by simp)
    simpa only [green_square_eq_double_kernel, Pi.zero_apply, sub_self, Int.cast_zero,
      zero_pow (by omega : 2 ≠ 0), Finset.sum_const_zero, add_zero, div_one] using h
  have hlog : Tendsto (fun t : ℕ => Real.log (t : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hdiff : Tendsto (fun t : ℕ => (∑' y : Site 4, greenTime 4 t 0 y ^ 2) /
      Real.log t - 4 / Real.pi ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ ((tendsto_const_nhds (x := C)).div_atTop hlog)
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with t ht
    have hL : 0 < Real.log (t : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < t))
    have he : (∑' y : Site 4, greenTime 4 t 0 y ^ 2) / Real.log t - 4 / Real.pi ^ 2 =
        ((∑' y : Site 4, greenTime 4 t 0 y ^ 2) - 4 / Real.pi ^ 2 * Real.log t) / Real.log t := by
      field_simp
    rw [Real.norm_eq_abs, he, abs_div, abs_of_pos hL]
    exact div_le_div_of_nonneg_right (hb t ht) hL.le
  have h := (hdiff.add_const (4 / Real.pi ^ 2)).congr'
    (Eventually.of_forall fun t => show
      (∑' y : Site 4, greenTime 4 t 0 y ^ 2) / Real.log t - 4 / Real.pi ^ 2 + 4 / Real.pi ^ 2 =
        (∑' y : Site 4, greenTime 4 t 0 y ^ 2) / Real.log t from by ring)
  simpa only [zero_add] using h

theorem tendsto_membrane_gaussian_four (hPaired : External.PairedLocalCLTFour)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hsq : MemLp (id : ℝ → ℝ) 2 ν)
    (hmean : ∫ z, z ∂ν = 0) :
    TendstoInDistribution (fun (t : ℕ) (ζ : Site 4 → ℝ) => membrane ζ t 0 / Real.sqrt (Real.log t))
      atTop (id : ℝ → ℝ) (fun _ => LatticeProb.iidLaw 4 ν)
      (gaussianReal 0 (Real.toNNReal (4 * variance id ν / Real.pi ^ 2))) := by
  let N (t : ℕ) := (boxFinset (0 : Site 4) t).card
  let a (t : ℕ) (i : Fin (N t)) :=
    greenTime 4 t 0 (boxEnum (0 : Site 4) t i) / Real.sqrt (Real.log t)
  have hlog : Tendsto (fun t : ℕ => Real.log (t : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hQ : Tendsto (fun t : ℕ => ∑ i, a t i ^ 2) atTop (𝓝 (4 / Real.pi ^ 2)) := by
    refine (tendsto_green_square_div_log_four hPaired).congr' ?_
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with t ht
    have hL : 0 ≤ Real.log (t : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ t))
    dsimp [a, N]
    simp_rw [div_pow, Real.sq_sqrt hL]
    rw [← Finset.sum_div]
    congr 1
    rw [tsum_greenTime_sq_eq_sum]
    exact (sum_boxEnum (0 : Site 4) t (fun y => greenTime 4 t 0 y ^ 2)).symm
  have hsmall : ∀ δ : ℝ, 0 < δ → ∀ᶠ t : ℕ in atTop, ∀ i, |a t i| ≤ δ := by
    intro δ hδ
    have hscale : Tendsto (fun t : ℕ => (1 + 2 * LatticeProb.diagConst 4) /
        Real.sqrt (Real.log t)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hlog)
    filter_upwards [hscale.eventually (gt_mem_nhds hδ)] with t ht i
    have hg : greenTime 4 t 0 (boxEnum (0 : Site 4) t i) ≤ 1 + 2 * LatticeProb.diagConst 4 := by
      rw [greenTime_eq_srwGreen]
      exact LatticeProb.srwGreen_four_le t _
    dsimp only [a]
    rw [abs_of_nonneg (div_nonneg (greenTime_nonneg _ _ _) (Real.sqrt_nonneg _))]
    exact (div_le_div_of_nonneg_right hg (Real.sqrt_nonneg _)).trans ht.le
  have hclt := weighted_iid_central_limit_pick ν hsq hmean N a
    (fun t => boxEnum (0 : Site 4) t) (fun t => boxEnum_injective _ _) hsmall
    (4 / Real.pi ^ 2) hQ
  have he (t : ℕ) (ζ : Site 4 → ℝ) :
      (∑ i, a t i * ζ (boxEnum (0 : Site 4) t i)) = membrane ζ t 0 / Real.sqrt (Real.log t) := by
    dsimp [a, N]
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div, ← membrane_eq_sum_boxEnum]
  have hv : variance id ν = ∫ z, z ^ 2 ∂ν := by
    rw [variance_eq_integral measurable_id.aemeasurable]
    simp only [id_eq, hmean, sub_zero]
  have hvQ : (∫ z, z ^ 2 ∂ν) * (4 / Real.pi ^ 2) = 4 * variance id ν / Real.pi ^ 2 := by
    rw [← hv]
    ring
  simpa only [he, hvQ] using hclt


theorem tendsto_membrane_variance_four (hPaired : External.PairedLocalCLTFour)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hsq : MemLp (id : ℝ → ℝ) 2 ν) :
    Tendsto (fun t : ℕ => variance (fun ζ => membrane ζ t 0) (LatticeProb.iidLaw 4 ν) /
      Real.log t) atTop (𝓝 (4 * variance id ν / Real.pi ^ 2)) := by
  rw [show 4 * variance id ν / Real.pi ^ 2 = variance id ν * (4 / Real.pi ^ 2) by ring]
  simpa only [variance_membrane ν hsq, mul_div_assoc] using
    (tendsto_green_square_div_log_four hPaired).const_mul (variance id ν)

end Sandpile
