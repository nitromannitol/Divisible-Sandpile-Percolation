import Sandpile.Support.D4DoubleHeatFar

/-!
# A uniform logarithmic form of the doubled heat kernel

Combining the near-distance logarithmic approximation with the far-distance
bound gives one estimate valid at every displacement: the double heat-kernel
sum differs by a constant from `4/π²` times the positive part of
`log(t/(1+|x-y|²))`.
-/

namespace Sandpile

/-- Uniform logarithmic approximation of the doubled four-dimensional heat
kernel, valid at every displacement and every time at least two. -/
theorem exists_double_heat_kernel_four_log_bound (hPaired : External.PairedLocalCLTFour) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℕ, 2 ≤ t → ∀ x y : Site 4,
      |(∑ a ∈ Finset.range t, ∑ b ∈ Finset.range t, heatKernel 4 (a + b) x y) -
        4 / Real.pi ^ 2 * max 0 (Real.log ((t : ℝ) /
          (1 + ∑ i : Fin 4, ((x i - y i : ℤ) : ℝ) ^ 2)))| ≤ C := by
  obtain ⟨Cnear, hnear⟩ := exists_double_heat_kernel_four_bound hPaired
  obtain ⟨Cfar, hCfar, hfar⟩ := exists_double_heat_kernel_four_far_bound hPaired
  let c : ℝ := 4 / Real.pi ^ 2
  let C := max Cnear 0 + Cfar + c * Real.log 2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro t ht x y
  let q : ℝ := ∑ i : Fin 4, ((x i - y i : ℤ) : ℝ) ^ 2
  let S : ℝ := ∑ a ∈ Finset.range t, ∑ b ∈ Finset.range t, heatKernel 4 (a + b) x y
  have hq : 0 ≤ q := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have ht2 : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0 : ℝ) < t := by linarith
  have hd : 0 < 1 + q := by linarith
  have harg : 0 < (t : ℝ) / (1 + q) := div_pos ht0 hd
  by_cases hqt : q ≤ t
  · have hbase : |S - c * Real.log ((t : ℝ) / (1 + q))| ≤ max Cnear 0 :=
      (hnear t ht x y hqt).trans (le_max_left _ _)
    have hratio : (1 / 2 : ℝ) ≤ (t : ℝ) / (1 + q) := by
      rw [le_div_iff₀ hd]
      nlinarith
    have hloglo : -Real.log 2 ≤ Real.log ((t : ℝ) / (1 + q)) := by
      have h := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) hratio
      have heq : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
        rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
      linarith
    have hchange : |c * Real.log ((t : ℝ) / (1 + q)) -
        c * max 0 (Real.log ((t : ℝ) / (1 + q)))| ≤ c * Real.log 2 := by
      by_cases hlog : 0 ≤ Real.log ((t : ℝ) / (1 + q))
      · rw [max_eq_right hlog, sub_self, abs_zero]
        positivity
      · have hn : Real.log ((t : ℝ) / (1 + q)) ≤ 0 := le_of_not_ge hlog
        rw [max_eq_left hn, mul_zero, sub_zero, abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hc hn)]
        nlinarith
    have h := (abs_sub_le S (c * Real.log ((t : ℝ) / (1 + q)))
      (c * max 0 (Real.log ((t : ℝ) / (1 + q))))).trans (add_le_add hbase hchange)
    dsimp [C]
    linarith
  · have hqt' : (t : ℝ) ≤ q := le_of_lt (lt_of_not_ge hqt)
    have hS : S ≤ Cfar := hfar t (by omega) x y hqt'
    have hS0 : 0 ≤ S := by
      exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => heatKernel_nonneg _ _ _
    have hratio : (t : ℝ) / (1 + q) ≤ 1 := by
      rw [div_le_one hd]
      linarith
    have hlog : Real.log ((t : ℝ) / (1 + q)) ≤ 0 := Real.log_nonpos harg.le hratio
    rw [show max 0 (Real.log ((t : ℝ) / (1 + q))) = 0 from max_eq_left hlog,
      mul_zero, sub_zero, abs_of_nonneg hS0]
    dsimp [C]
    linarith [le_max_right Cnear 0, mul_nonneg hc hlog2]

end Sandpile
