/-
Paired time-step estimates for doubled sums of a nonnegative heat kernel.
The summable remainder is retained after weighting each pair by its time.
-/
import LatticeProb.Walk.WindowD4
import LatticeProb.Walk.GreenSq

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile

/-- Summing the inverse squares over an interval starting at one gives a uniform bound. -/
theorem sum_Ico_inv_sq_le_two (n : ℕ) :
    ∑ s ∈ Finset.Ico 1 n, ((s : ℝ) ^ 2)⁻¹ ≤ 2 := by
  simpa using LatticeProb.sum_Ico_inv_sq_le (m := 1) (by omega) n

/-- A paired kernel estimate loses only bounded terms when weighted by time. -/
theorem sum_time_pair_identity (f : ℕ → ℝ) (t : ℕ) (ht : 1 ≤ t) :
    ∑ s ∈ Finset.Ico 1 t, (s : ℝ) * (f s + f (s + 1)) =
      2 * (∑ s ∈ Finset.Ico 1 t, (s : ℝ) * f s) -
        (∑ s ∈ Finset.Ico 1 t, f s) + ((t : ℝ) - 1) * f t := by
  induction t, ht using Nat.le_induction with
  | base => simp
  | succ t ht ih =>
    rw [Finset.sum_Ico_succ_top ht, Finset.sum_Ico_succ_top ht,
      Finset.sum_Ico_succ_top ht, ih]
    push_cast
    ring


theorem double_sum_sub_weighted_bound (f : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀ n, 0 ≤ f n) (hf0 : f 0 ≤ M)
    (hbound : ∀ n : ℕ, 1 ≤ n → f n ≤ M / (n : ℝ) ^ 2)
    (t : ℕ) (ht : 1 ≤ t) :
    |(∑ a ∈ Finset.range t, ∑ b ∈ Finset.range t, f (a + b)) -
      (∑ s ∈ Finset.Ico 1 t, (s : ℝ) * f s)| ≤ 5 * M := by
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  have hsmall : ∑ s ∈ Finset.Ico 1 t, f s ≤ 2 * M := by
    calc ∑ s ∈ Finset.Ico 1 t, f s ≤
        ∑ s ∈ Finset.Ico 1 t, M * ((s : ℝ) ^ 2)⁻¹ := by
          apply Finset.sum_le_sum
          intro s hs
          simpa only [div_eq_mul_inv] using hbound s (Finset.mem_Ico.mp hs).1
      _ = M * ∑ s ∈ Finset.Ico 1 t, ((s : ℝ) ^ 2)⁻¹ := (Finset.mul_sum ..).symm
      _ ≤ M * 2 := mul_le_mul_of_nonneg_left (sum_Ico_inv_sq_le_two t) hM
      _ = 2 * M := by ring
  have hsplit : (∑ a ∈ Finset.range t, ∑ b ∈ Finset.range t, f (a + b)) =
      (∑ s ∈ Finset.range t, ((s : ℝ) + 1) * f s) +
        ∑ s ∈ Finset.Ico t (t + t), (LatticeProb.pairCount t t s : ℝ) * f s := by
    rw [LatticeProb.sum_sum_add_eq,
      ← Finset.sum_range_add_sum_Ico _ (show t ≤ t + t from by omega)]
    congr 1
    apply Finset.sum_congr rfl
    intro s hs
    rw [LatticeProb.pairCount_of_lt (Finset.mem_range.mp hs) (Finset.mem_range.mp hs)]
    push_cast
    rfl
  have htail0 : 0 ≤ ∑ s ∈ Finset.Ico t (t + t),
      (LatticeProb.pairCount t t s : ℝ) * f s :=
    Finset.sum_nonneg fun s _ => mul_nonneg (Nat.cast_nonneg _) (hf s)
  have htail : ∑ s ∈ Finset.Ico t (t + t),
      (LatticeProb.pairCount t t s : ℝ) * f s ≤ 2 * M := by
    calc ∑ s ∈ Finset.Ico t (t + t), (LatticeProb.pairCount t t s : ℝ) * f s ≤
        ∑ s ∈ Finset.Ico t (t + t), (t : ℝ) * (M * ((s : ℝ) ^ 2)⁻¹) := by
          apply Finset.sum_le_sum
          intro s hs
          apply mul_le_mul
          · exact_mod_cast (LatticeProb.pairCount_le t t s).trans (min_le_right _ _)
          · simpa only [div_eq_mul_inv] using hbound s (ht.trans (Finset.mem_Ico.mp hs).1)
          · exact hf s
          · positivity
      _ = (t : ℝ) * M * ∑ s ∈ Finset.Ico t (t + t), ((s : ℝ) ^ 2)⁻¹ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        ring
      _ ≤ (t : ℝ) * M * (2 / t) :=
        mul_le_mul_of_nonneg_left (LatticeProb.sum_Ico_inv_sq_le ht (t + t)) (by positivity)
      _ = 2 * M := by field_simp
  have hlow : (∑ s ∈ Finset.range t, ((s : ℝ) + 1) * f s) =
      (∑ s ∈ Finset.Ico 1 t, (s : ℝ) * f s) + f 0 +
        ∑ s ∈ Finset.Ico 1 t, f s := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (show 0 < t from ht)]
    simp only [Nat.cast_zero, zero_add, one_mul]
    simp_rw [add_mul, one_mul]
    rw [Finset.sum_add_distrib]
    ring
  rw [hsplit, hlow]
  rw [abs_of_nonneg (by linarith [hf 0, Finset.sum_nonneg (fun s (_ : s ∈ Finset.Ico 1 t) => hf s)])]
  linarith


theorem double_sum_paired_approx (f : ℕ → ℝ) (M C A q : ℝ) (hM : 0 ≤ M)
    (hf : ∀ n, 0 ≤ f n) (hf0 : f 0 ≤ M)
    (hbound : ∀ n : ℕ, 1 ≤ n → f n ≤ M / (n : ℝ) ^ 2)
    (hpair : ∀ n : ℕ, 1 ≤ n →
      |f n + f (n + 1) - A / (n : ℝ) ^ 2 * Real.exp (-2 * q / n)| ≤ C / (n : ℝ) ^ 3)
    (hC : 0 ≤ C) (t : ℕ) (ht : 1 ≤ t) :
    |(∑ a ∈ Finset.range t, ∑ b ∈ Finset.range t, f (a + b)) -
        A / 2 * (∑ s ∈ Finset.Ico 1 t, Real.exp (-2 * q / s) / s)| ≤ 7 * M + C := by
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  set S := ∑ s ∈ Finset.Ico 1 t, (s : ℝ) * f s
  set P := ∑ s ∈ Finset.Ico 1 t, (s : ℝ) * (f s + f (s + 1))
  set J := ∑ s ∈ Finset.Ico 1 t, Real.exp (-2 * q / s) / s
  have hsmall : ∑ s ∈ Finset.Ico 1 t, f s ≤ 2 * M := by
    calc ∑ s ∈ Finset.Ico 1 t, f s ≤
        ∑ s ∈ Finset.Ico 1 t, M * ((s : ℝ) ^ 2)⁻¹ := by
          apply Finset.sum_le_sum
          intro s hs
          simpa only [div_eq_mul_inv] using hbound s (Finset.mem_Ico.mp hs).1
      _ = M * ∑ s ∈ Finset.Ico 1 t, ((s : ℝ) ^ 2)⁻¹ := (Finset.mul_sum ..).symm
      _ ≤ M * 2 := mul_le_mul_of_nonneg_left (sum_Ico_inv_sq_le_two t) hM
      _ = 2 * M := by ring
  have htf : ((t : ℝ) - 1) * f t ≤ M := by
    have hfT := hbound t ht
    have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
    have h : f t * (t : ℝ) ^ 2 ≤ M := (le_div_iff₀ (sq_pos_of_pos htpos)).mp hfT
    nlinarith [hf t]
  have hSP : |S - P / 2| ≤ 2 * M := by
    have he : P = 2 * S - (∑ s ∈ Finset.Ico 1 t, f s) + ((t : ℝ) - 1) * f t :=
      sum_time_pair_identity f t ht
    have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
    have hs0 : 0 ≤ ∑ s ∈ Finset.Ico 1 t, f s := Finset.sum_nonneg fun s _ => hf s
    have htf0 : 0 ≤ ((t : ℝ) - 1) * f t := mul_nonneg (by linarith) (hf t)
    rw [abs_le]
    constructor <;> linarith
  have hPJ : |P - A * J| ≤ 2 * C := by
    have he : P - A * J = ∑ s ∈ Finset.Ico 1 t,
        (s : ℝ) * (f s + f (s + 1) - A / (s : ℝ) ^ 2 * Real.exp (-2 * q / s)) := by
      dsimp [P, J]
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro s hs
      have hspos : (0 : ℝ) < s := by exact_mod_cast (Finset.mem_Ico.mp hs).1
      field_simp
    rw [he]
    calc |∑ s ∈ Finset.Ico 1 t,
          (s : ℝ) * (f s + f (s + 1) - A / (s : ℝ) ^ 2 * Real.exp (-2 * q / s))| ≤
        ∑ s ∈ Finset.Ico 1 t, |(s : ℝ) *
          (f s + f (s + 1) - A / (s : ℝ) ^ 2 * Real.exp (-2 * q / s))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s ∈ Finset.Ico 1 t, C * ((s : ℝ) ^ 2)⁻¹ := by
        apply Finset.sum_le_sum
        intro s hs
        have hs1 := (Finset.mem_Ico.mp hs).1
        have hspos : (0 : ℝ) < s := by exact_mod_cast hs1
        rw [abs_mul, abs_of_pos hspos]
        calc (s : ℝ) * |f s + f (s + 1) - A / (s : ℝ) ^ 2 * Real.exp (-2 * q / s)| ≤
            (s : ℝ) * (C / (s : ℝ) ^ 3) := mul_le_mul_of_nonneg_left (hpair s hs1) hspos.le
          _ = C * ((s : ℝ) ^ 2)⁻¹ := by field_simp
      _ = C * ∑ s ∈ Finset.Ico 1 t, ((s : ℝ) ^ 2)⁻¹ := (Finset.mul_sum ..).symm
      _ ≤ C * 2 := mul_le_mul_of_nonneg_left (sum_Ico_inv_sq_le_two t) hC
      _ = 2 * C := by ring
  have hPJ2 : |P / 2 - A / 2 * J| ≤ C := by
    rw [show P / 2 - A / 2 * J = (P - A * J) / 2 by ring, abs_div]
    norm_num
    linarith
  have hDS := double_sum_sub_weighted_bound f M hM hf hf0 hbound t ht
  have h := abs_sub_le (∑ a ∈ Finset.range t, ∑ b ∈ Finset.range t, f (a + b)) S (A / 2 * J)
  have h' := abs_sub_le S (P / 2) (A / 2 * J)
  dsimp only [S] at hSP h h'
  dsimp only [J] at hPJ2 h h'
  linarith

end Sandpile
