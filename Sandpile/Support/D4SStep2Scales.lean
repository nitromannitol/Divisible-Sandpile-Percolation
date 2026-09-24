/-
The scale bookkeeping of Step 2 of `prop:d4-superdiffusive-limit`
(`sandpile.tex:3366-3382`).

Step 2 runs at the intermediate scale `n_R = ⌊R\sqrt{t_R}⌋` inside the time
`t_R = ⌊R^\alpha⌋`, and its two displays need four facts about those scales for
large `R`: the window is nonempty, it is at most half the time, the remaining
time `t_R-n_R` is at least three so that `\log\log` is defined and nonnegative,
and the second moment at `t_R-n_R` is below the second moment at `t_R`.  The
second display also needs the new limit `((1+\log\log t_R)^2+M)R^{-\sigma}\to0`,
which is where its rate `R^{-\min\{s,1\}}` beats the growth of the second
moment.
-/
import Sandpile.Support.D4SScaleSq

open LatticeProb

open Filter Topology

namespace Sandpile.D4Super

/-- **The second display's limit**: any positive power of `1/R` beats the square
of the iterated logarithm of `t_R`. -/
theorem tendsto_loglog_mul_rpow_inv (α : ℝ) (hα : 2 < α) (M σ : ℝ) (hM : 0 ≤ M) (hσ : 0 < σ) :
    Tendsto (fun R : ℝ => ((1 + Real.log (Real.log (⌊R ^ α⌋₊ : ℝ))) ^ 2 + M) * (R⁻¹) ^ σ)
      atTop (𝓝 0) := by
  have hmaj : Tendsto (fun R : ℝ => ((1 + Real.sqrt M) + α * Real.log R) ^ 2 / R ^ σ)
      atTop (𝓝 0) := tendsto_sq_affine_log_div_rpow α (1 + Real.sqrt M) σ hσ
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with R hR
    have h0 := (loglog_floor_rpow_bounds α hα R hR).1
    have hR0 : (0:ℝ) < R := by linarith
    have hp : (0:ℝ) < (R⁻¹) ^ σ := Real.rpow_pos_of_pos (by positivity) σ
    positivity
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with R hR
    obtain ⟨h0, hle⟩ := loglog_floor_rpow_bounds α hα R hR
    have hR0 : (0:ℝ) < R := by linarith
    have hinv : (R⁻¹ : ℝ) ^ σ = (R ^ σ)⁻¹ := by
      rw [← Real.rpow_neg_one R, ← Real.rpow_mul hR0.le, ← Real.rpow_neg hR0.le]
      ring_nf
    have hD : (0:ℝ) < R ^ σ := Real.rpow_pos_of_pos hR0 σ
    have hsq : (1 + Real.log (Real.log (⌊R ^ α⌋₊ : ℝ))) ^ 2 + M ≤
        ((1 + Real.sqrt M) + α * Real.log R) ^ 2 := by
      have h1 : 1 + Real.log (Real.log (⌊R ^ α⌋₊ : ℝ)) ≤ 1 + α * Real.log R := by linarith
      have h2 : (0:ℝ) ≤ 1 + Real.log (Real.log (⌊R ^ α⌋₊ : ℝ)) := by linarith
      have h3 : (1 + Real.log (Real.log (⌊R ^ α⌋₊ : ℝ))) ^ 2 ≤ (1 + α * Real.log R) ^ 2 :=
        pow_le_pow_left₀ h2 h1 2
      have hMs : Real.sqrt M ^ 2 = M := Real.sq_sqrt hM
      have hMs0 : (0:ℝ) ≤ Real.sqrt M := Real.sqrt_nonneg M
      have hax : (0:ℝ) ≤ 1 + α * Real.log R := by nlinarith
      nlinarith [h3, hMs, hMs0, hax]
    rw [hinv, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right hsq hD.le

/-- The square of a real power is the power at twice the exponent. -/
theorem rpow_sq_eq (x σ : ℝ) (hx : 0 ≤ x) : (x ^ σ) ^ 2 = x ^ (2 * σ) := by
  have h : ((2:ℕ) : ℝ) = (2:ℝ) := by norm_num
  rw [← Real.rpow_natCast (x ^ σ) 2, ← Real.rpow_mul hx, h]
  ring_nf

/-- The same limit at the natural-number exponent two. -/
theorem tendsto_loglog_mul_inv_sq (α : ℝ) (hα : 2 < α) (M : ℝ) (hM : 0 ≤ M) :
    Tendsto (fun R : ℝ => ((1 + Real.log (Real.log (⌊R ^ α⌋₊ : ℝ))) ^ 2 + M) * (R⁻¹) ^ 2)
      atTop (𝓝 0) := by
  refine (tendsto_loglog_mul_rpow_inv α hα M 2 hM (by norm_num)).congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
  have hcast : ((2:ℕ) : ℝ) = (2:ℝ) := by norm_num
  have h := Real.rpow_natCast (R⁻¹) 2
  rw [hcast] at h
  rw [h]

/-- **The four facts about the scales of Step 2**, for large `R`. -/
theorem eventually_step2_scales (α : ℝ) (hα : 2 < α) :
    ∀ᶠ R : ℝ in atTop, (2:ℝ) ≤ R ∧
      1 ≤ ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ ∧
      ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ ≤ ⌊R ^ α⌋₊ ∧
      3 ≤ ⌊R ^ α⌋₊ - ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ := by
  have hpow : Tendsto (fun R : ℝ => R ^ α) atTop atTop := tendsto_rpow_atTop (by linarith)
  filter_upwards [eventually_ge_atTop (2:ℝ), nR_le_half_floor α hα,
    hpow.eventually_ge_atTop (8:ℝ)] with R hR hhalf hbig
  have ht4 : (4:ℝ) ≤ (⌊R ^ α⌋₊ : ℝ) := four_le_floor_rpow α hα R hR
  have ht8 : (8:ℕ) ≤ ⌊R ^ α⌋₊ := Nat.le_floor (by exact_mod_cast hbig)
  have ht8' : (8:ℝ) ≤ (⌊R ^ α⌋₊ : ℝ) := by exact_mod_cast ht8
  have hsq : (2:ℝ) ≤ Real.sqrt (⌊R ^ α⌋₊ : ℝ) := by
    rw [show (2:ℝ) = Real.sqrt 4 by rw [show (4:ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt ht4
  have hn1 : 1 ≤ ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ := by
    refine Nat.le_floor ?_
    push_cast
    nlinarith
  have hnt : ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ ≤ ⌊R ^ α⌋₊ := by
    have : (⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ : ℝ) ≤ (⌊R ^ α⌋₊ : ℝ) := by linarith
    exact_mod_cast this
  refine ⟨hR, hn1, hnt, ?_⟩
  have h3 : (3:ℝ) ≤ (⌊R ^ α⌋₊ : ℝ) - (⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ : ℝ) := by linarith
  have hcast : ((⌊R ^ α⌋₊ - ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ : ℕ) : ℝ)
      = (⌊R ^ α⌋₊ : ℝ) - (⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ : ℝ) := Nat.cast_sub hnt
  have : (3:ℝ) ≤ ((⌊R ^ α⌋₊ - ⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ : ℕ) : ℝ) := by rw [hcast]; linarith
  exact_mod_cast this

/-- The second moment at the earlier time `t-n` is below the second moment at
`t`: `\log\log` is nondecreasing above three. -/
theorem sq_loglog_mono {m t : ℕ} (hm : 3 ≤ m) (hmt : m ≤ t) (M : ℝ) :
    (1 + Real.log (Real.log (m : ℝ))) ^ 2 + M ≤ (1 + Real.log (Real.log (t : ℝ))) ^ 2 + M := by
  have hm3 : (3:ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have ht3 : (3:ℝ) ≤ (t : ℝ) := le_trans hm3 (by exact_mod_cast hmt)
  obtain ⟨hlm, hllm, -, -⟩ := Sandpile.log_time_bounds_four hm3
  obtain ⟨hlt, hllt, -, -⟩ := Sandpile.log_time_bounds_four ht3
  have hmono : Real.log (Real.log (m : ℝ)) ≤ Real.log (Real.log (t : ℝ)) :=
    Real.log_le_log (by linarith) (Real.log_le_log (by linarith) (by exact_mod_cast hmt))
  have h1 : (0:ℝ) ≤ 1 + Real.log (Real.log (m : ℝ)) := by linarith
  have h2 : 1 + Real.log (Real.log (m : ℝ)) ≤ 1 + Real.log (Real.log (t : ℝ)) := by linarith
  nlinarith [pow_le_pow_left₀ h1 h2 2]

end Sandpile.D4Super
