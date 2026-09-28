import Sandpile.Support.DoubleSum
import Sandpile.Support.ExponentialHarmonic
import Sandpile.External.PairedLocalCLTFour
import Sandpile.External.VarianceScaleProved

/-!
# The doubled heat-kernel logarithmic coefficient in dimension four

This file identifies the exact logarithmic coefficient `4/π²` in the asymptotics of the doubled
heat kernel sum `∑_{a,b<t} heatKernel 4 (a+b) x y` in dimension four, up to an additive constant
uniform in `t`, `x` and `y`. The local-limit remainder of the two-step sum enters through the
explicit paired estimate `Sandpile.External.PairedLocalCLTFour`, which is combined with a
telescoped comparison between the exponential-weighted harmonic sum and the target logarithm.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile

/-- The doubled heat-kernel sum `∑_{a,b<t} heatKernel 4 (a+b) x y`, for `t ≥ 2` and squared
displacement `q = ∑ (x i - y i)^2` at most `t`, agrees with `4/π² * log(t/(1+q))` up to an
additive constant `C` independent of `t`, `x` and `y`, given the paired local CLT input
`hPaired`. -/
theorem exists_double_heat_kernel_four_bound (hPaired : External.PairedLocalCLTFour) :
    ∃ C : ℝ, ∀ t : ℕ, 2 ≤ t → ∀ x y : Site 4,
      (∑ i : Fin 4, ((x i - y i : ℤ) : ℝ) ^ 2) ≤ (t : ℝ) →
      |(∑ a ∈ Finset.range t, ∑ b ∈ Finset.range t, heatKernel 4 (a + b) x y) -
        4 / Real.pi ^ 2 * Real.log ((t : ℝ) /
          (1 + ∑ i : Fin 4, ((x i - y i : ℤ) : ℝ) ^ 2))| ≤ C := by
  obtain ⟨C, hC, hpair⟩ := hPaired
  set M := max 1 (LatticeProb.diagConst 4)
  have hM1 : 1 ≤ M := le_max_left _ _
  have hM : 0 ≤ M := by linarith
  refine ⟨7 * M + C + 40 / Real.pi ^ 2, ?_⟩
  intro t ht x y hq
  set q := ∑ i : Fin 4, ((x i - y i : ℤ) : ℝ) ^ 2
  have hq0 : 0 ≤ q := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have ht1 : 1 ≤ t := by omega
  have hbound : ∀ n : ℕ, 1 ≤ n → heatKernel 4 n x y ≤ M / (n : ℝ) ^ 2 := by
    intro n hn
    rw [heatKernel_eq_srwHeat]
    exact (LatticeProb.srwHeat_four_le hn (y - x)).trans
      (div_le_div_of_nonneg_right (le_max_right _ _) (sq_nonneg _))
  have hf0 : heatKernel 4 0 x y ≤ M := by
    change (if x = y then (1 : ℝ) else 0) ≤ M
    split_ifs <;> linarith
  have hpair' : ∀ n : ℕ, 1 ≤ n →
      |heatKernel 4 n x y + heatKernel 4 (n + 1) x y -
        (8 / Real.pi ^ 2) / (n : ℝ) ^ 2 * Real.exp (-2 * q / n)| ≤ C / (n : ℝ) ^ 3 := by
    intro n hn
    simpa only [div_div] using hpair n hn x y
  have hD := double_sum_paired_approx (fun n => heatKernel 4 n x y) M C
    (8 / Real.pi ^ 2) q hM (fun n => heatKernel_nonneg n x y) hf0 hbound hpair' hC.le t ht1
  have hJ := abs_exp_inverse_sum_sub_log_le q hq0 t ht1 hq
  have hpipos : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have he : (8 / Real.pi ^ 2) / 2 = 4 / Real.pi ^ 2 := by ring
  rw [he] at hD
  have herror : |4 / Real.pi ^ 2 * (∑ s ∈ Finset.Ico 1 t, Real.exp (-2 * q / s) / s) -
      4 / Real.pi ^ 2 * Real.log ((t : ℝ) / (1 + q))| ≤ 40 / Real.pi ^ 2 := by
    rw [← mul_sub, abs_mul, abs_of_pos (div_pos (by norm_num) hpipos)]
    calc 4 / Real.pi ^ 2 * |(∑ s ∈ Finset.Ico 1 t, Real.exp (-2 * q / s) / s) -
          Real.log ((t : ℝ) / (1 + q))| ≤ 4 / Real.pi ^ 2 * 10 :=
          mul_le_mul_of_nonneg_left hJ (by positivity)
      _ = 40 / Real.pi ^ 2 := by ring
  exact (abs_sub_le _ (4 / Real.pi ^ 2 *
    (∑ s ∈ Finset.Ico 1 t, Real.exp (-2 * q / s) / s)) _).trans (add_le_add hD herror)

end Sandpile
