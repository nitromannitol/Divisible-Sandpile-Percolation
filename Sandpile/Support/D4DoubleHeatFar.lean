import Sandpile.Support.DoubleHeatKernel

/-!
# The doubled heat kernel at large displacement

In dimension four, the double sum of transition probabilities is uniformly
bounded when the squared displacement is at least the time horizon. The paired
local central limit theorem reduces the sum to a damped harmonic sum, whose
early part is bounded uniformly.
-/

namespace Sandpile

/-- The doubled four-dimensional heat kernel is uniformly bounded at squared
displacements at least the time horizon. -/
theorem exists_double_heat_kernel_four_far_bound (hPaired : External.PairedLocalCLTFour) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℕ, 1 ≤ t → ∀ x y : Site 4,
      (t : ℝ) ≤ ∑ i : Fin 4, ((x i - y i : ℤ) : ℝ) ^ 2 →
      (∑ a ∈ Finset.range t, ∑ b ∈ Finset.range t, heatKernel 4 (a + b) x y) ≤ C := by
  obtain ⟨C, hC, hpair⟩ := hPaired
  let M := max 1 (LatticeProb.diagConst 4)
  have hM1 : 1 ≤ M := le_max_left _ _
  have hM : 0 ≤ M := by linarith
  refine ⟨7 * M + C + 16 / Real.pi ^ 2, by positivity, ?_⟩
  intro t ht x y hfar
  let q := ∑ i : Fin 4, ((x i - y i : ℤ) : ℝ) ^ 2
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
    (8 / Real.pi ^ 2) q hM (fun n => heatKernel_nonneg n x y) hf0 hbound hpair' hC.le t ht
  have hJ := exp_inverse_early_sum_le q t ht (by dsimp [q]; linarith)
  have hpipos : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hmul : (8 / Real.pi ^ 2) / 2 *
      (∑ s ∈ Finset.Ico 1 t, Real.exp (-2 * q / s) / s) ≤ 16 / Real.pi ^ 2 := by
    calc
      _ ≤ (8 / Real.pi ^ 2) / 2 * 4 := mul_le_mul_of_nonneg_left hJ (by positivity)
      _ = 16 / Real.pi ^ 2 := by ring
  have hupper := (abs_le.mp hD).2
  linarith

end Sandpile
