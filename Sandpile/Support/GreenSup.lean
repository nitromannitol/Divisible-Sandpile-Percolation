/-
The supremum of the truncated Green kernel in dimensions one to three.

`thm:critical-toppling` normalizes the membrane field by its own standard
deviation, and the third absolute moment of the resulting coefficients is
controlled by `sup_x g_n(0,x)` against `∑_x g_n(0,x)^2`.  The supremum grows
like `√n` in dimension one, like `1 + log n` in dimension two, and is bounded in
dimension three; all three come from the on-diagonal bound
`p_k(x,y) ≤ C k^{-d/2}` summed over `k < n`.
-/
import Sandpile.Support.Kernel
import Sandpile.External.VarianceScaleProved
import LatticeProb.Walk.SRWSup
import LatticeProb.Walk.Series

namespace Sandpile

variable {d : ℕ}

/-! ### Three power sums -/

/-- `∑_{1 ≤ k < n} k^{-1/2} ≤ 2√n`. -/
theorem sum_Ico_rpow_neg_half_le (n : ℕ) :
    ∑ k ∈ Finset.Ico 1 n, ((k : ℝ) ^ (-(1 : ℝ) / 2)) ≤ 2 * Real.sqrt (n : ℝ) := by
  have hterm : ∀ k : ℕ, ((k : ℝ) ^ (-(1 : ℝ) / 2)) = (1 : ℝ) / Real.sqrt (k : ℝ) := by
    intro k
    have h := LatticeProb.rpow_neg_half_eq 1 k
    rw [Nat.cast_one, pow_one] at h
    rw [h, one_div]
  rw [Finset.sum_congr rfl (fun k _ => hterm k), Finset.sum_Ico_eq_sum_range]
  have hcast : ∀ r : ℕ,
      (1 : ℝ) / Real.sqrt (((1 + r : ℕ) : ℝ)) = (1 : ℝ) / Real.sqrt ((r : ℝ) + 1) := by
    intro r; push_cast; ring_nf
  rw [Finset.sum_congr rfl (fun r _ => hcast r)]
  refine (LatticeProb.sum_inv_sqrt_le (n - 1)).trans ?_
  have : Real.sqrt (((n - 1 : ℕ) : ℝ)) ≤ Real.sqrt (n : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast Nat.sub_le n 1)
  linarith

/-- `∑_{1 ≤ k < n} k^{-1} ≤ 1 + log n`. -/
theorem sum_Ico_rpow_neg_one_le (n : ℕ) :
    ∑ k ∈ Finset.Ico 1 n, ((k : ℝ) ^ (-(2 : ℝ) / 2)) ≤ 1 + Real.log (n : ℝ) := by
  have hterm : ∀ k : ℕ, ((k : ℝ) ^ (-(2 : ℝ) / 2)) = ((k : ℝ))⁻¹ := by
    intro k
    rw [show (-(2 : ℝ) / 2) = (-1 : ℝ) by norm_num, Real.rpow_neg_one]
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  exact LatticeProb.sum_inv_le_one_add_log n

/-- `∑_{1 ≤ k < n} k^{-3/2} ≤ 3`. -/
theorem sum_Ico_rpow_neg_three_half_le (n : ℕ) :
    ∑ k ∈ Finset.Ico 1 n, ((k : ℝ) ^ (-(3 : ℝ) / 2)) ≤ 3 :=
  LatticeProb.sum_rpow_three_halves_le n

/-! ### The bound -/

/-- The truncated Green kernel against the on-diagonal bound. -/
theorem greenTime_le_one_add_sum (hd : 1 ≤ d) (n : ℕ) (x y : Site d) :
    greenTime d n x y ≤ 1 + Real.sqrt 2 ^ d * LatticeProb.greenConst d *
      ∑ k ∈ Finset.Ico 1 n, ((k : ℝ) ^ (-(d : ℝ) / 2)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [greenTime, LatticeProb.greenTime]
  · have hA : (0 : ℝ) ≤ Real.sqrt 2 ^ d * LatticeProb.greenConst d :=
      mul_nonneg (by positivity) (LatticeProb.greenConst_nonneg d)
    have h0 : heatKernel d 0 x y ≤ 1 := by
      show (if x = y then (1 : ℝ) else 0) ≤ 1
      split <;> norm_num
    have hrest : ∑ k ∈ Finset.Ico 1 n, heatKernel d k x y
        ≤ ∑ k ∈ Finset.Ico 1 n,
            Real.sqrt 2 ^ d * LatticeProb.greenConst d * ((k : ℝ) ^ (-(d : ℝ) / 2)) := by
      refine Finset.sum_le_sum fun k hk => ?_
      have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
      rw [heatKernel_eq_srwHeat]
      exact LatticeProb.srwHeat_sup_bound (by omega) hk1 (y - x)
    rw [← Finset.mul_sum] at hrest
    show (∑ k ∈ Finset.range n, heatKernel d k x y) ≤
        1 + Real.sqrt 2 ^ d * LatticeProb.greenConst d *
          ∑ k ∈ Finset.Ico 1 n, ((k : ℝ) ^ (-(d : ℝ) / 2))
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hn]
    linarith

/-- The rate of growth of `sup_x g_n(0,x)` in dimensions one to three: `√n`,
`1 + log n`, and a constant. -/
noncomputable def greenSupRate (d n : ℕ) : ℝ :=
  if d = 1 then Real.sqrt (n : ℝ) else if d = 2 then 1 + Real.log (n : ℝ) else 1

theorem greenSupRate_nonneg (d n : ℕ) : 0 ≤ greenSupRate d n := by
  unfold greenSupRate
  split
  · positivity
  · split
    · have : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
      linarith
    · norm_num

/-- **The supremum of the truncated Green kernel in dimensions one to three.** -/
theorem exists_greenTime_sup_le (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (x y : Site d),
      greenTime d n x y ≤ C * greenSupRate d n := by
  set A : ℝ := Real.sqrt 2 ^ d * LatticeProb.greenConst d with hAdef
  have hA : (0 : ℝ) ≤ A := mul_nonneg (by positivity) (LatticeProb.greenConst_nonneg d)
  interval_cases d
  · -- dimension one
    refine ⟨1 + 2 * A, by linarith, fun n x y => ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [greenTime, LatticeProb.greenTime, greenSupRate]
    · have h1 := greenTime_le_one_add_sum (d := 1) le_rfl n x y
      have h2 : ∑ k ∈ Finset.Ico 1 n, ((k : ℝ) ^ (-((1 : ℕ) : ℝ) / 2))
          ≤ 2 * Real.sqrt (n : ℝ) := by
        rw [Nat.cast_one]; exact sum_Ico_rpow_neg_half_le n
      have hs : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
        rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
        exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
      have : greenSupRate 1 n = Real.sqrt (n : ℝ) := by simp [greenSupRate]
      rw [this]
      nlinarith
  · -- dimension two
    refine ⟨1 + A, by linarith, fun n x y => ?_⟩
    have h1 := greenTime_le_one_add_sum (d := 2) (by norm_num) n x y
    have h2 : ∑ k ∈ Finset.Ico 1 n, ((k : ℝ) ^ (-((2 : ℕ) : ℝ) / 2))
        ≤ 1 + Real.log (n : ℝ) := by
      rw [show ((2 : ℕ) : ℝ) = (2 : ℝ) from by norm_num]
      exact sum_Ico_rpow_neg_one_le n
    have hlog : (0 : ℝ) ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
    have : greenSupRate 2 n = 1 + Real.log (n : ℝ) := by simp [greenSupRate]
    rw [this]
    nlinarith
  · -- dimension three
    refine ⟨1 + 3 * A, by linarith, fun n x y => ?_⟩
    have h1 := greenTime_le_one_add_sum (d := 3) (by norm_num) n x y
    have h2 : ∑ k ∈ Finset.Ico 1 n, ((k : ℝ) ^ (-((3 : ℕ) : ℝ) / 2)) ≤ 3 := by
      rw [show ((3 : ℕ) : ℝ) = (3 : ℝ) from by norm_num]
      exact sum_Ico_rpow_neg_three_half_le n
    have : greenSupRate 3 n = 1 := by norm_num [greenSupRate]
    rw [this]
    nlinarith

end Sandpile
