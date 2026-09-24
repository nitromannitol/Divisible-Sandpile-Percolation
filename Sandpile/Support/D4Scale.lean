/-
The smoothing scale in Step 4 of `prop:d4-pointwise-linearization`.
Taking one plus a natural floor keeps the smoothing time positive.  Its
rounding error contributes `log(t+2)/t`, which has an exponential bound
throughout the intermediate range of deviation levels.
-/
import Sandpile.Support.D4Difference

open LatticeProb

namespace Sandpile

theorem log_time_bounds_four {t : ℝ} (ht : 3 ≤ t) :
    1 ≤ Real.log t ∧ 1 ≤ 1 + Real.log (Real.log t) ∧
      1 ≤ Real.log (t + 2) ∧ Real.log (t + 2) ≤ Real.log t + 1 := by
  have ht0 : 0 < t := by linarith
  have hlog : 1 ≤ Real.log t :=
    one_le_log_three.trans (Real.log_le_log (by norm_num) ht)
  refine ⟨hlog, by linarith [Real.log_nonneg hlog],
    hlog.trans (Real.log_le_log ht0 (by linarith)), ?_⟩
  have h2 : Real.log (t + 2) ≤ Real.log (2 * t) :=
    Real.log_le_log (by linarith) (by linarith)
  rw [Real.log_mul (by norm_num) ht0.ne'] at h2
  linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]

theorem log_time_mul_exp_neg_four {t : ℝ} (ht : 3 ≤ t) :
    Real.log (t + 2) * Real.exp (-(2 * (1 + Real.log (Real.log t)))) ≤ 2 := by
  obtain ⟨hlog, hell, -, hL⟩ := log_time_bounds_four ht
  have h1 : Real.log t ≤ Real.exp (2 * (1 + Real.log (Real.log t))) := by
    calc Real.log t = Real.exp (Real.log (Real.log t)) :=
        (Real.exp_log (by linarith)).symm
      _ ≤ Real.exp (2 * (1 + Real.log (Real.log t))) :=
        Real.exp_le_exp.mpr (by linarith)
  have h2 := mul_le_mul_of_nonneg_right (show Real.log (t + 2) ≤
      2 * Real.exp (2 * (1 + Real.log (Real.log t))) by linarith)
    (Real.exp_pos (-(2 * (1 + Real.log (Real.log t))))).le
  simpa [mul_assoc, ← Real.exp_add] using h2

theorem log_time_div_time_four {t : ℝ} (ht : 3 ≤ t) :
    Real.log (t + 2) / t ≤ 4 * Real.exp (-(Real.log (t + 2) / 2)) := by
  have ht0 : 0 < t := by linarith
  set L := Real.log (t + 2)
  have h1 : L ≤ 2 * Real.exp (L / 2) := by
    have := le_exp_self (L / 2)
    linarith
  have h2 : Real.exp (L / 2) ≤ 2 * t * Real.exp (-(L / 2)) := by
    have h := mul_le_mul_of_nonneg_right (show t + 2 ≤ 2 * t by linarith)
      (Real.exp_pos (-(L / 2))).le
    have hid : (t + 2) * Real.exp (-(L / 2)) = Real.exp (L / 2) := by
      rw [← Real.exp_log (by linarith : 0 < t + 2), ← Real.exp_add]
      congr 1
      dsimp [L]
      ring
    rwa [hid] at h
  rw [div_le_iff₀ ht0]
  nlinarith

/-- A positive integer smoothing scale with a short logarithmic window. -/
theorem exists_linearization_scale_four (t : ℕ) (ht : 3 ≤ t) (lam : ℝ) (hlam : 1 ≤ lam) :
    ∃ n : ℕ, 1 ≤ n ∧ n < t ∧ (n : ℝ) ≤ 2 * (t : ℝ) / 3 ∧
      (n : ℝ) ≤ (t : ℝ) * Real.exp (-(2 * (1 + Real.log (Real.log t)) + lam)) + 1 ∧
      1 + Real.log (((t : ℝ) + 2) / ((n : ℝ) + 2)) ≤
        4 * (1 + Real.log (Real.log t) + lam) := by
  have ht3 : (3 : ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0 : ℝ) < t := by linarith
  obtain ⟨-, hell, -, hL⟩ := log_time_bounds_four ht3
  set ell := 1 + Real.log (Real.log t)
  set q := (t : ℝ) * Real.exp (-(2 * ell + lam))
  have hq : 0 < q := mul_pos ht0 (Real.exp_pos _)
  set n := ⌊q⌋₊ + 1
  have hn1 : 1 ≤ n := by omega
  have hnq : (n : ℝ) ≤ q + 1 := by
    dsimp [n]
    push_cast
    linarith [Nat.floor_le hq.le]
  have hqn : q < (n : ℝ) := by simpa [n] using Nat.lt_floor_add_one q
  have he : Real.exp (-(2 * ell + lam)) ≤ 1 / 4 := by
    rw [Real.exp_neg, inv_eq_one_div]
    have h1 : (3 : ℝ) ≤ 2 * ell + lam := by dsimp [ell]; linarith
    have h2 : (4 : ℝ) ≤ Real.exp (2 * ell + lam) := by
      have := Real.add_one_le_exp (2 * ell + lam)
      linarith
    exact one_div_le_one_div_of_le (by norm_num) h2
  have hn23 : (n : ℝ) ≤ 2 * (t : ℝ) / 3 := by
    have h := mul_le_mul_of_nonneg_left he ht0.le
    dsimp [q] at hnq
    linarith
  have hnt : n < t := by
    have : (n : ℝ) < t := by linarith
    exact_mod_cast this
  refine ⟨n, hn1, hnt, hn23, hnq, ?_⟩
  have hn0 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hlogq : Real.log q = Real.log t - (2 * ell + lam) := by
    dsimp [q]
    rw [Real.log_mul ht0.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  have hlogn : Real.log q ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_le_log hq (by linarith)
  rw [Real.log_div (by positivity) hn0.ne']
  rw [hlogq] at hlogn
  dsimp [ell] at hlogn
  linarith

/-- A window of logarithmic size at most `4(ell+lam)` gives the desired
Bernstein exponent, with a fixed numerical loss. -/
theorem linearization_exponent_four {ell lam W n : ℝ}
    (hell : 0 < ell) (hlam : 0 ≤ lam) (hW : 0 < W)
    (hWle : W ≤ 4 * (ell + lam)) (hn : 1 ≤ n) :
    min (lam ^ 2 / ell) lam / 32 ≤ min ((lam / 2) ^ 2 / W) (lam / 2 * n) := by
  set m := min (lam ^ 2 / ell) lam
  have hm0 : 0 ≤ m := le_min (div_nonneg (sq_nonneg _) hell.le) hlam
  have hm1 : m ≤ lam := min_le_right _ _
  have hm2 : m * ell ≤ lam ^ 2 := (le_div_iff₀ hell).mp (min_le_left _ _)
  apply le_min
  · rw [le_div_iff₀ hW]
    have h := mul_le_mul_of_nonneg_left hWle hm0
    have hml : m * lam ≤ lam ^ 2 := by nlinarith
    nlinarith
  · have := mul_le_mul_of_nonneg_left hn hlam
    nlinarith

/-- The rounding error in the smoothing time is exponentially small for
levels bounded by a fixed multiple of `log(t+2)`. -/
theorem linearization_scale_markov_four {t lam B n M Y : ℝ}
    (ht : 3 ≤ t) (hlam : 1 ≤ lam) (hB : 1 ≤ B)
    (hlamB : lam ≤ B * Real.log (t + 2))
    (hn : n ≤ 2 * t / 3)
    (hnq : n ≤ t * Real.exp (-(2 * (1 + Real.log (Real.log t)) + lam)) + 1)
    (hM : 0 ≤ M) (hY : 0 ≤ Y)
    (hwindow : (t - n) * Y ≤ n * (M * Real.log (t + 2))) :
    2 * Y / (lam / 2) ≤ 72 * M * Real.exp (-(lam / (2 * B))) := by
  have ht0 : 0 < t := by linarith
  have hB0 : 0 < 2 * B := by linarith
  obtain ⟨-, -, hL, -⟩ := log_time_bounds_four ht
  set L := Real.log (t + 2)
  set ell := 1 + Real.log (Real.log t)
  set E := Real.exp (-(lam / (2 * B)))
  have hE : 0 < E := Real.exp_pos _
  have hexp1 : Real.exp (-lam) ≤ E := by
    apply Real.exp_le_exp.mpr
    have : lam / (2 * B) ≤ lam := (div_le_iff₀ hB0).mpr (by nlinarith)
    linarith
  have hexp2 : Real.exp (-(L / 2)) ≤ E := by
    apply Real.exp_le_exp.mpr
    have : lam / (2 * B) ≤ L / 2 := (div_le_iff₀ hB0).mpr (by nlinarith)
    linarith
  have hsmall : L * Real.exp (-(2 * ell + lam)) ≤ 2 * E := by
    rw [neg_add, Real.exp_add, ← mul_assoc]
    calc L * Real.exp (-(2 * ell)) * Real.exp (-lam)
        ≤ 2 * Real.exp (-lam) :=
          mul_le_mul_of_nonneg_right (log_time_mul_exp_neg_four ht) (Real.exp_pos _).le
      _ ≤ 2 * E := by linarith
  have hround : L / t ≤ 4 * E :=
    (log_time_div_time_four ht).trans (by linarith)
  have hnL : L * n / t ≤ 6 * E := by
    have h1 := mul_le_mul_of_nonneg_left hnq (show 0 ≤ L by dsimp [L]; linarith)
    have h2 : L * n / t ≤ L * Real.exp (-(2 * ell + lam)) + L / t := by
      apply (div_le_iff₀ ht0).mpr
      have hdiv : L / t * t = L := div_mul_cancel₀ L ht0.ne'
      nlinarith
    linarith
  have hYt : Y ≤ 3 * M * (L * n / t) := by
    have h1 := mul_le_mul_of_nonneg_right hn hY
    have h2 : t * Y ≤ 3 * M * L * n := by
      dsimp [L]
      nlinarith
    have h3 : Y ≤ (3 * M * L * n) / t := (le_div_iff₀ ht0).mpr (by nlinarith)
    convert h3 using 1
    ring
  have hYbound : Y ≤ 18 * M * E := by
    have := mul_le_mul_of_nonneg_left hnL (show 0 ≤ 3 * M by positivity)
    nlinarith [hYt]
  have hmarkov : 2 * Y / (lam / 2) ≤ 4 * Y := by
    rw [div_le_iff₀ (by linarith : 0 < lam / 2)]
    nlinarith
  nlinarith

end Sandpile
