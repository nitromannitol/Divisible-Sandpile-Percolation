import Sandpile.Support.D4ScaleSep
import Sandpile.Support.D4ScaleSepSecond
import Sandpile.Support.D4Scale

/-!
# The two limits of the superdiffusive scale separation

The two limits of `eq:d4-superdiffusive-scale-separation` (`sandpile.tex:3334-3336`), which fix
the intermediate scale in the proof of `prop:d4-superdiffusive-limit`. With `t_R = ⌊R^α⌋` and
`n_R = ⌊R √t_R⌋` for `α > 2`,

  `R²(1 + log log t_R) / n_R → 0`   and   `n_R log²(t_R + 2) / (t_R − n_R) → 0`,

proved by `tendsto_scale_sep_first` and `tendsto_scale_sep_second`. `Support/D4ScaleSep.lean` and
`Support/D4ScaleSepSecond.lean` majorize the two quotients by `4(1 + log log t_R)/R^{α/2−1}` and
`8 log²(R^α + 2)/R^{α/2−1}`, both for `R ≥ 2`, the second under the side condition `n_R ≤ t_R/2`
(`nR_le_half_floor`). What is added here is that both majorants vanish
(`tendsto_affine_log_div_rpow`, `tendsto_sq_affine_log_div_rpow`), and that the side condition
holds for large `R`. The mechanism in each case is the same: the numerator grows like a
polynomial in `log R` and the denominator like a positive power of `R`, so
`Real.isLittleO_log_rpow_atTop` closes it. The first numerator is an iterated logarithm, bounded
by `α log R` through `log y ≤ y − 1` (`loglog_floor_rpow_bounds`); the second is a square
(`log_rpow_add_two_bounds`), handled by splitting `R^{α/2−1}` into two equal factors. The side
condition `n_R ≤ t_R/2` is `4R² ≤ t_R`, which holds once `R^{α−2} ≥ 5`; this is the only place
`α > 2` is used quantitatively, and it is why the scale separation fails at diffusive times.
-/

open Real Filter Topology

namespace Sandpile.D4Super


/-- An affine function of `log R` divided by a positive power of `R` tends to `0`, via
`Real.isLittleO_log_rpow_atTop`. -/
theorem tendsto_affine_log_div_rpow (a b c : ℝ) (hc : 0 < c) :
    Tendsto (fun R : ℝ => (b + a * Real.log R) / R ^ c) atTop (𝓝 0) := by
  have h1 : Tendsto (fun R : ℝ => R ^ c) atTop atTop := tendsto_rpow_atTop hc
  have h2 : Tendsto (fun R : ℝ => (R ^ c)⁻¹) atTop (𝓝 0) := h1.inv_tendsto_atTop
  have h3 : Tendsto (fun R : ℝ => Real.log R / R ^ c) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop hc).tendsto_div_nhds_zero
  have h4 : Tendsto (fun R : ℝ => (R ^ c)⁻¹ * b + a * (Real.log R / R ^ c)) atTop (𝓝 0) := by
    have := (h2.mul_const b).add (h3.const_mul a)
    simpa using this
  refine h4.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  have hRc : (R : ℝ) ^ c ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hR c)
  field_simp

/-- The square of an affine function of `log R` divided by a positive power of `R` tends to `0`,
by squaring `tendsto_affine_log_div_rpow` with the exponent halved. -/
theorem tendsto_sq_affine_log_div_rpow (a b c : ℝ) (hc : 0 < c) :
    Tendsto (fun R : ℝ => (b + a * Real.log R) ^ 2 / R ^ c) atTop (𝓝 0) := by
  have hc2 : 0 < c / 2 := by linarith
  have h4 : Tendsto (fun R : ℝ => ((b + a * Real.log R) / R ^ (c / 2)) ^ 2) atTop (𝓝 0) := by
    have := (tendsto_affine_log_div_rpow a b (c / 2) hc2).pow 2
    simpa using this
  refine h4.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  have hRc : (R : ℝ) ^ (c / 2) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hR (c / 2))
  have hsplit : (R : ℝ) ^ c = R ^ (c / 2) * R ^ (c / 2) := by
    rw [← Real.rpow_add hR]
    ring_nf
  rw [hsplit, div_pow]
  field_simp

/-- For `R ≥ 2` and `α > 2` the time `t_R = ⌊R^α⌋₊` is at least `4`. -/
theorem four_le_floor_rpow (α : ℝ) (hα : 2 < α) (R : ℝ) (hR : 2 ≤ R) :
    (4 : ℝ) ≤ (⌊R ^ α⌋₊ : ℝ) := by
  have hR0 : (0 : ℝ) < R := by linarith
  have h1 : (2 : ℝ) ^ (2 : ℝ) ≤ (2 : ℝ) ^ α :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h2 : (2 : ℝ) ^ α ≤ R ^ α := Real.rpow_le_rpow (by norm_num) hR (by linarith)
  have h3 : ((2 : ℝ) ^ (2 : ℝ)) = 4 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have h4 : (4 : ℝ) ≤ R ^ α := by rw [← h3]; linarith
  have : (4 : ℕ) ≤ ⌊R ^ α⌋₊ := Nat.le_floor (by exact_mod_cast h4)
  exact_mod_cast this

/-- The iterated logarithm of `t_R = ⌊R^α⌋₊` is nonnegative and at most `α log R`. -/
theorem loglog_floor_rpow_bounds (α : ℝ) (hα : 2 < α) (R : ℝ) (hR : 2 ≤ R) :
    0 ≤ Real.log (Real.log (⌊R ^ α⌋₊ : ℝ)) ∧
      Real.log (Real.log (⌊R ^ α⌋₊ : ℝ)) ≤ α * Real.log R := by
  have hR0 : (0 : ℝ) < R := by linarith
  have ht4 : (4 : ℝ) ≤ (⌊R ^ α⌋₊ : ℝ) := four_le_floor_rpow α hα R hR
  obtain ⟨hlog1, hlog2, -, -⟩ := Sandpile.log_time_bounds_four (t := (⌊R ^ α⌋₊ : ℝ)) (by linarith)
  have hlogR : 0 < Real.log R := Real.log_pos (by linarith)
  have hαR : 0 < α * Real.log R := by positivity
  have htle : (⌊R ^ α⌋₊ : ℝ) ≤ R ^ α := Nat.floor_le (by positivity)
  have hlogle : Real.log (⌊R ^ α⌋₊ : ℝ) ≤ α * Real.log R := by
    have := Real.log_le_log (by linarith) htle
    rwa [Real.log_rpow hR0] at this
  refine ⟨by linarith, ?_⟩
  have h1 : Real.log (Real.log (⌊R ^ α⌋₊ : ℝ)) ≤ Real.log (α * Real.log R) :=
    Real.log_le_log (by linarith) hlogle
  have h2 : Real.log (α * Real.log R) ≤ α * Real.log R - 1 :=
    Real.log_le_sub_one_of_pos hαR
  linarith

/-- **The first limit of `eq:d4-superdiffusive-scale-separation`.** -/
theorem tendsto_scale_sep_first (α : ℝ) (hα : 2 < α) :
    Tendsto (fun R : ℝ => R ^ 2 * (1 + Real.log (Real.log (⌊R ^ α⌋₊ : ℝ)))
        / (⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ : ℝ)) atTop (𝓝 0) := by
  have hc : 0 < α / 2 - 1 := by linarith
  have hmaj : Tendsto (fun R : ℝ => 4 * ((1 + α * Real.log R) / R ^ (α / 2 - 1)))
      atTop (𝓝 0) := by
    simpa using (tendsto_affine_log_div_rpow α 1 (α / 2 - 1) hc).const_mul 4
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with R hR
    have := (loglog_floor_rpow_bounds α hα R hR).1
    positivity
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with R hR
    obtain ⟨h0, hle⟩ := loglog_floor_rpow_bounds α hα R hR
    refine (scale_sep_first_bound α hα R hR).trans ?_
    have hD : (0 : ℝ) < R ^ (α / 2 - 1) := Real.rpow_pos_of_pos (by linarith) _
    rw [mul_div_assoc]
    gcongr


/-- Eventually the intermediate scale `n_R = ⌊R √t_R⌋₊` is at most half of `t_R = ⌊R^α⌋₊`. -/
theorem nR_le_half_floor (α : ℝ) (hα : 2 < α) :
    ∀ᶠ R : ℝ in atTop,
      (⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ : ℝ) ≤ (⌊R ^ α⌋₊ : ℝ) / 2 := by
  have hpow : Tendsto (fun R : ℝ => R ^ (α - 2)) atTop atTop :=
    tendsto_rpow_atTop (by linarith)
  filter_upwards [eventually_ge_atTop (2 : ℝ), hpow.eventually_ge_atTop 5] with R hR hbig
  have hR0 : (0 : ℝ) < R := by linarith
  have hsplit : R ^ α = R ^ (2 : ℕ) * R ^ (α - 2) := by
    rw [show (2 : ℕ) = ((2 : ℕ) : ℕ) from rfl, ← Real.rpow_natCast R 2, ← Real.rpow_add hR0]
    norm_num
  have hsq : (4 : ℝ) ≤ R ^ (2 : ℕ) := by nlinarith
  have hge : 4 * R ^ (2 : ℕ) ≤ R ^ α := by
    rw [hsplit]; nlinarith [sq_nonneg R]
  have hfl : R ^ α - 1 < (⌊R ^ α⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one (R ^ α)
    linarith
  have ht4 : 4 * R ^ (2 : ℕ) ≤ (⌊R ^ α⌋₊ : ℝ) := by nlinarith
  have ht0 : (0 : ℝ) ≤ (⌊R ^ α⌋₊ : ℝ) := by positivity
  have hsqrt : 2 * R ≤ Real.sqrt (⌊R ^ α⌋₊ : ℝ) := by
    have h1 : Real.sqrt ((2 * R) ^ 2) ≤ Real.sqrt (⌊R ^ α⌋₊ : ℝ) :=
      Real.sqrt_le_sqrt (by nlinarith)
    rwa [Real.sqrt_sq (by linarith)] at h1
  have hs0 : 0 ≤ Real.sqrt (⌊R ^ α⌋₊ : ℝ) := Real.sqrt_nonneg _
  have hprod : R * Real.sqrt (⌊R ^ α⌋₊ : ℝ) ≤ (⌊R ^ α⌋₊ : ℝ) / 2 := by
    nlinarith [Real.sq_sqrt ht0]
  exact le_trans (Nat.floor_le (by positivity)) hprod


/-- For `R ≥ 2` the logarithm of `R^α + 2` is nonnegative and at most `log 2 + α log R`. -/
theorem log_rpow_add_two_bounds (α : ℝ) (hα : 2 < α) (R : ℝ) (hR : 2 ≤ R) :
    0 ≤ Real.log (R ^ α + 2) ∧ Real.log (R ^ α + 2) ≤ Real.log 2 + α * Real.log R := by
  have hR0 : (0 : ℝ) < R := by linarith
  have ht4 : (4 : ℝ) ≤ (⌊R ^ α⌋₊ : ℝ) := four_le_floor_rpow α hα R hR
  have hRα : (4 : ℝ) ≤ R ^ α := le_trans ht4 (Nat.floor_le (by positivity))
  refine ⟨Real.log_nonneg (by linarith), ?_⟩
  have h1 : Real.log (R ^ α + 2) ≤ Real.log (2 * R ^ α) :=
    Real.log_le_log (by linarith) (by linarith)
  rwa [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hR0] at h1

/-- **The second limit of `eq:d4-superdiffusive-scale-separation`.** -/
theorem tendsto_scale_sep_second (α : ℝ) (hα : 2 < α) :
    Tendsto (fun R : ℝ =>
        (⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ : ℝ) * Real.log ((⌊R ^ α⌋₊ : ℝ) + 2) ^ 2
          / ((⌊R ^ α⌋₊ : ℝ) - (⌊R * Real.sqrt (⌊R ^ α⌋₊ : ℝ)⌋₊ : ℝ))) atTop (𝓝 0) := by
  have hc : 0 < α / 2 - 1 := by linarith
  have hmaj : Tendsto (fun R : ℝ =>
      8 * ((Real.log 2 + α * Real.log R) ^ 2 / R ^ (α / 2 - 1))) atTop (𝓝 0) := by
    simpa using (tendsto_sq_affine_log_div_rpow α (Real.log 2) (α / 2 - 1) hc).const_mul 8
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [eventually_ge_atTop (2 : ℝ), nR_le_half_floor α hα] with R hR hhalf
    have ht0 : (0 : ℝ) ≤ (⌊R ^ α⌋₊ : ℝ) := by positivity
    refine div_nonneg (by positivity) ?_
    linarith
  · filter_upwards [eventually_ge_atTop (2 : ℝ), nR_le_half_floor α hα] with R hR hhalf
    obtain ⟨hl0, hlle⟩ := log_rpow_add_two_bounds α hα R hR
    refine (scale_sep_second_bound α hα R hR hhalf).trans ?_
    have hD : (0 : ℝ) < R ^ (α / 2 - 1) := Real.rpow_pos_of_pos (by linarith) _
    rw [mul_div_assoc]
    gcongr

end Sandpile.D4Super
