/-
Uniform double-exponential decay for a quadratic probability recurrence.
-/
import Sandpile.Support.RealBoxes

open scoped ENNReal

namespace Sandpile

lemma exists_double_exponential_bound (c₀ C₀ c C B : ℝ)
    (hc₀ : 0 < c₀) (hC₀ : 0 < C₀) (hc : 0 < c) (hC : 0 < C) (hB : 1 ≤ B) :
    ∃ b η M : ℝ, 0 < b ∧ 0 < η ∧ 1 ≤ M ∧
      ∀ m : ℝ, M ≤ m → ∀ q : ℕ → ℝ≥0∞,
        q 0 ≤ ENNReal.ofReal (C₀ * Real.exp (-(c₀ * m))) →
        (∀ n : ℕ, q (n + 1) ≤ ENNReal.ofReal C * q n ^ 2 +
          ENNReal.ofReal (C * B ^ n * Real.exp (-(c * m * (2 : ℝ) ^ n)))) →
        ∀ n : ℕ, q n ≤ ENNReal.ofReal (η * Real.exp (-(b * m * (2 : ℝ) ^ n))) := by
  let η := 1 / (2 * C)
  have hη : 0 < η := by dsimp [η]; positivity
  let b := min (c₀ / 2) (c / 4)
  have hb : 0 < b := lt_min (by positivity) (by positivity)
  have hb₀ : b ≤ c₀ / 2 := min_le_left _ _
  have hbc : b ≤ c / 4 := min_le_right _ _
  let L₀ := |Real.log C₀| + |Real.log η|
  let L := |Real.log C| + |Real.log (η / 2)| + Real.log B
  let M := max 1 (max (2 * L₀ / c₀) (2 * L / c))
  have hM : 1 ≤ M := le_max_left _ _
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
  have hηsq : C * η ^ 2 = η / 2 := by
    dsimp only [η]
    field_simp
  have hrepr (A : ℝ) (hA : 0 < A) (z : ℝ) :
      A * Real.exp z = Real.exp (Real.log A + z) := by
    rw [Real.exp_add, Real.exp_log hA]
  have hreprB (n : ℕ) (z : ℝ) :
      C * B ^ n * Real.exp z = Real.exp (Real.log C + (n : ℝ) * Real.log B + z) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_nat_mul, Real.exp_log hC, Real.exp_log hB0]
  have hn (n : ℕ) : (n : ℝ) ≤ (2 : ℝ) ^ n := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [Nat.cast_add, Nat.cast_one, pow_succ]
      have hh : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
      linarith
  refine ⟨b, η, M, hb, hη, hM, ?_⟩
  intro m hm q hq₀ hqstep
  have hm1 : 1 ≤ m := hM.trans hm
  have hm0 : 0 ≤ m := by linarith
  have hmL₀ : L₀ ≤ c₀ / 2 * m := by
    have hh : 2 * L₀ / c₀ ≤ m :=
      (le_max_left _ _).trans ((le_max_right _ _).trans hm)
    have hh' := (div_le_iff₀ hc₀).mp hh
    linarith
  have hmL : L ≤ c / 2 * m := by
    have hh : 2 * L / c ≤ m :=
      (le_max_right _ _).trans ((le_max_right _ _).trans hm)
    have hh' := (div_le_iff₀ hc).mp hh
    linarith
  have hbase : C₀ * Real.exp (-(c₀ * m)) ≤ η * Real.exp (-(b * m)) := by
    rw [hrepr C₀ hC₀, hrepr η hη]
    apply Real.exp_le_exp.mpr
    have hgap := mul_le_mul_of_nonneg_right hb₀ hm0
    have hlog₀ := le_abs_self (Real.log C₀)
    have hlogη := neg_le_abs (Real.log η)
    dsimp only [L₀] at hmL₀
    linarith
  have herr (n : ℕ) : C * B ^ n * Real.exp (-(c * m * (2 : ℝ) ^ n)) ≤
      η / 2 * Real.exp (-(b * m * (2 : ℝ) ^ (n + 1))) := by
    have htwo : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    have ht0 : 0 ≤ (2 : ℝ) ^ n := by positivity
    have hscale := mul_le_mul_of_nonneg_right hmL ht0
    have hgap := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (show c / 2 ≤ c - 2 * b by linarith) hm0) ht0
    have hlogs : |Real.log C| + |Real.log (η / 2)| ≤
        (|Real.log C| + |Real.log (η / 2)|) * (2 : ℝ) ^ n := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left htwo
        (add_nonneg (abs_nonneg _) (abs_nonneg _))
    have hnlog := mul_le_mul_of_nonneg_right (hn n) hlogB
    have hlogC := le_abs_self (Real.log C)
    have hlogη := neg_le_abs (Real.log (η / 2))
    rw [hreprB n, hrepr (η / 2) (by positivity)]
    apply Real.exp_le_exp.mpr
    rw [pow_succ]
    dsimp only [L] at hscale
    nlinarith
  have hquad (n : ℕ) : C * (η * Real.exp (-(b * m * (2 : ℝ) ^ n))) ^ 2 =
      η / 2 * Real.exp (-(b * m * (2 : ℝ) ^ (n + 1))) := by
    rw [mul_pow, pow_two (Real.exp _), ← Real.exp_add, ← mul_assoc, hηsq]
    congr 1
    congr 1
    rw [pow_succ]
    ring
  intro n
  induction n with
  | zero => simpa only [pow_zero, mul_one] using hq₀.trans (ENNReal.ofReal_le_ofReal hbase)
  | succ n ih =>
    calc
      _ ≤ ENNReal.ofReal C * q n ^ 2 +
          ENNReal.ofReal (C * B ^ n * Real.exp (-(c * m * (2 : ℝ) ^ n))) := hqstep n
      _ ≤ ENNReal.ofReal C * (ENNReal.ofReal (η * Real.exp (-(b * m * (2 : ℝ) ^ n)))) ^ 2 +
          ENNReal.ofReal (C * B ^ n * Real.exp (-(c * m * (2 : ℝ) ^ n))) :=
        add_le_add (mul_le_mul' le_rfl (pow_le_pow_left₀ zero_le ih 2)) le_rfl
      _ = ENNReal.ofReal (η / 2 * Real.exp (-(b * m * (2 : ℝ) ^ (n + 1)))) +
          ENNReal.ofReal (C * B ^ n * Real.exp (-(c * m * (2 : ℝ) ^ n))) := by
        rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul hC.le, hquad]
      _ ≤ ENNReal.ofReal (η / 2 * Real.exp (-(b * m * (2 : ℝ) ^ (n + 1)))) +
          ENNReal.ofReal (η / 2 * Real.exp (-(b * m * (2 : ℝ) ^ (n + 1)))) :=
        add_le_add le_rfl (ENNReal.ofReal_le_ofReal (herr n))
      _ = ENNReal.ofReal (η * Real.exp (-(b * m * (2 : ℝ) ^ (n + 1)))) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

end Sandpile
