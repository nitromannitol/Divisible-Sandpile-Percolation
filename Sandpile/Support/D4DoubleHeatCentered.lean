import Sandpile.Support.D4DoubleHeatLog

/-!
# Centering the logarithmic double heat kernel

The positive part of a logarithm is one-Lipschitz. Consequently the
space-dependent truncated logarithm in the double heat kernel can be
recentered at an arbitrary spatial scale with an error controlled by the
logarithm of the ratio of squared distances.
-/

namespace Sandpile

/-- Replacing the denominator inside a positive-part logarithm costs at most the
absolute logarithm of the denominator ratio. -/
theorem abs_logPos_div_sub_le (t a b : ℝ) (ht : 0 < t) (ha : 0 < a) (hb : 0 < b) :
    |max 0 (Real.log (t / a)) - max 0 (Real.log (t / b))| ≤ |Real.log (a / b)| := by
  have h := abs_max_sub_max_le_abs (Real.log (t / a)) (Real.log (t / b)) (0 : ℝ)
  have h' : |max 0 (Real.log (t / a)) - max 0 (Real.log (t / b))| ≤
      |Real.log (t / a) - Real.log (t / b)| := by
    simpa only [max_comm] using h
  refine h'.trans_eq ?_
  rw [Real.log_div ht.ne' ha.ne', Real.log_div ht.ne' hb.ne', Real.log_div ha.ne' hb.ne']
  have he : Real.log t - Real.log a - (Real.log t - Real.log b) =
      -(Real.log a - Real.log b) := by ring
  rw [he, abs_neg]

/-- The doubled heat kernel, after subtracting the logarithm at a reference
scale, is controlled by the logarithmic ratio of its spatial denominator to
that scale, uniformly in time. -/
theorem exists_double_heat_kernel_four_centered_bound
    (hPaired : External.PairedLocalCLTFour) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℕ, 2 ≤ t → ∀ R : ℝ, 0 < R → ∀ x y : Site 4,
      |(∑ a ∈ Finset.range t, ∑ b ∈ Finset.range t, heatKernel 4 (a + b) x y) -
        4 / Real.pi ^ 2 * max 0 (Real.log ((t : ℝ) / R ^ 2))| ≤
      C + 4 / Real.pi ^ 2 * |Real.log ((1 +
        ∑ i : Fin 4, ((x i - y i : ℤ) : ℝ) ^ 2) / R ^ 2)| := by
  obtain ⟨C, hC, hlog⟩ := exists_double_heat_kernel_four_log_bound hPaired
  refine ⟨C, hC, ?_⟩
  intro t ht R hR x y
  let q : ℝ := ∑ i : Fin 4, ((x i - y i : ℤ) : ℝ) ^ 2
  let S : ℝ := ∑ a ∈ Finset.range t, ∑ b ∈ Finset.range t, heatKernel 4 (a + b) x y
  let c : ℝ := 4 / Real.pi ^ 2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hq : 0 ≤ q := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  have hnear : |S - c * max 0 (Real.log ((t : ℝ) / (1 + q)))| ≤ C := hlog t ht x y
  have hshift := abs_logPos_div_sub_le (t : ℝ) (1 + q) (R ^ 2)
    ht0 (by linarith) (sq_pos_of_pos hR)
  have hmul : |c * max 0 (Real.log ((t : ℝ) / (1 + q))) -
      c * max 0 (Real.log ((t : ℝ) / R ^ 2))| ≤
      c * |Real.log ((1 + q) / R ^ 2)| := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left hshift hc
  exact (abs_sub_le S (c * max 0 (Real.log ((t : ℝ) / (1 + q))))
    (c * max 0 (Real.log ((t : ℝ) / R ^ 2)))).trans (add_le_add hnear hmul)

end Sandpile
