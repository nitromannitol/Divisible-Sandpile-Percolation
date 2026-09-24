/-
The uniform Green weights of the rescaled odometer at the parabolic scale, the
coefficient bound behind the uniform exponential moment of
`sandpile.tex:1995-2007`.

Changing the scenery at a single site `z` changes `u_t(0)` by at most
`g_t(0,z)` times the change, so the rescaled odometer
`𝒰_R(1,0) = R^{-(2-d/2)}u_{⌊R²⌋}(0)` is coordinate Lipschitz with the weights
`R^{-(2-d/2)}g_{⌊R²⌋}(0,z)`.  In dimensions at most three the square sum of
those weights is bounded uniformly in `R`, because `eq:Qt-table` gives
`∑_z g_t(0,z)² ≤ C t^{(4-d)/2}` and the parabolic scale `t = ⌊R²⌋` turns
`t^{(4-d)/2}` into `R^{4-d}`, which is exactly the square of the scale factor.
The supremum of the weights is then bounded by the square root of the same
constant, so both norms that `lem:weighted-exp-conc` reads off the weights are
uniform in `R`.
-/
import Sandpile.External.VarianceScaleProved
import Sandpile.Support.FiniteCoord

open MeasureTheory ProbabilityTheory

namespace Sandpile.Support

variable {d : ℕ}

/-- For `1 ≤ d ≤ 3` the finite-time variance rate of `eq:Qt-table` is the real
power `t^{(4-d)/2}`. -/
theorem varianceRate_eq_rpow (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3) (t : ℕ) :
    Sandpile.External.Variance.varianceRate d t = (t : ℝ) ^ ((4 - (d : ℝ)) / 2) := by
  interval_cases d <;>
    simp [Sandpile.External.Variance.varianceRate] <;>
    norm_num

/-- The parabolic scaling absorbs the variance rate: at `t = ⌊R²⌋` the rate
`t^{(4-d)/2}` is at most the reciprocal of the square of the scale factor
`R^{-(2-d/2)}`. -/
theorem scaled_sq_bound (d : ℕ) (hd3 : d ≤ 3) (C : ℝ) (hC : 0 ≤ C)
    (R : ℝ) (hR : 1 ≤ R) (S : ℝ)
    (hS : S ≤ C * ((⌊R ^ 2⌋₊ : ℕ) : ℝ) ^ ((4 - (d : ℝ)) / 2)) :
    (R ^ (-(2 - (d : ℝ) / 2))) ^ 2 * S ≤ C := by
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR
  have hdR : (d : ℝ) ≤ 3 := by exact_mod_cast hd3
  have hexp : (0 : ℝ) ≤ (4 - (d : ℝ)) / 2 := by linarith
  have hfl : ((⌊R ^ 2⌋₊ : ℕ) : ℝ) ≤ R ^ 2 := Nat.floor_le (by positivity)
  have h2 : (R ^ 2 : ℝ) ^ ((4 - (d : ℝ)) / 2) = R ^ (4 - (d : ℝ)) := by
    rw [show (R ^ 2 : ℝ) = R ^ (2 : ℝ) by
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast],
      ← Real.rpow_mul hR0.le]
    ring_nf
  have hrate : ((⌊R ^ 2⌋₊ : ℕ) : ℝ) ^ ((4 - (d : ℝ)) / 2) ≤ R ^ (4 - (d : ℝ)) :=
    h2 ▸ Real.rpow_le_rpow (Nat.cast_nonneg _) hfl hexp
  have hsq : (R ^ (-(2 - (d : ℝ) / 2))) ^ 2 = R ^ (-(4 - (d : ℝ))) := by
    rw [show ((R ^ (-(2 - (d : ℝ) / 2))) ^ (2 : ℕ))
          = (R ^ (-(2 - (d : ℝ) / 2))) ^ ((2 : ℕ) : ℝ) by rw [Real.rpow_natCast],
      ← Real.rpow_mul hR0.le]
    ring_nf
  rw [hsq]
  have hpos : (0 : ℝ) < R ^ (-(4 - (d : ℝ))) := Real.rpow_pos_of_pos hR0 _
  have hstep : S ≤ C * R ^ (4 - (d : ℝ)) := le_trans hS (by nlinarith)
  calc R ^ (-(4 - (d : ℝ))) * S
      ≤ R ^ (-(4 - (d : ℝ))) * (C * R ^ (4 - (d : ℝ))) :=
        mul_le_mul_of_nonneg_left hstep hpos.le
    _ = C := by
        rw [show R ^ (-(4 - (d : ℝ))) * (C * R ^ (4 - (d : ℝ)))
              = C * (R ^ (-(4 - (d : ℝ))) * R ^ (4 - (d : ℝ))) by ring,
          ← Real.rpow_add hR0]
        simp

/-- The scale factor is at most one on `R ≥ 1` in dimensions at most three. -/
theorem rescale_factor_le_one (d : ℕ) (hd3 : d ≤ 3) (R : ℝ) (hR : 1 ≤ R) :
    R ^ (-(2 - (d : ℝ) / 2)) ≤ 1 := by
  have hdR : (d : ℝ) ≤ 3 := by exact_mod_cast hd3
  exact Real.rpow_le_one_of_one_le_of_nonpos hR (by linarith)

/-- The scale factor is positive. -/
theorem rescale_factor_pos (d : ℕ) (R : ℝ) (hR : 0 < R) :
    0 < R ^ (-(2 - (d : ℝ) / 2)) :=
  Real.rpow_pos_of_pos hR _

/-- **The square sum of the Green weights at the parabolic scale is bounded
uniformly in `R`.**  This is `eq:Qt-table` read at `t = ⌊R²⌋`, the first of the
two Green-kernel displays of `sandpile.tex:2003-2006`. -/
theorem exists_scaled_greenTime_sq_bound (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ R : ℝ, 1 ≤ R →
      (∑' z : Sandpile.Site d,
          (R ^ (-(2 - (d : ℝ) / 2)) * Sandpile.greenTime d ⌊R ^ 2⌋₊ 0 z) ^ 2) ≤ M := by
  obtain ⟨c, C, hc, hC, hQ⟩ := Sandpile.External.varianceScale.1 d hd
  refine ⟨max C 1, le_max_right _ _, ?_⟩
  intro R hR
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR
  set a : ℝ := R ^ (-(2 - (d : ℝ) / 2)) with ha
  have hsplit : (∑' z : Sandpile.Site d, (a * Sandpile.greenTime d ⌊R ^ 2⌋₊ 0 z) ^ 2)
      = a ^ 2 * ∑' z : Sandpile.Site d, Sandpile.greenTime d ⌊R ^ 2⌋₊ 0 z ^ 2 := by
    rw [← tsum_mul_left]
    exact tsum_congr fun z => by ring
  rw [hsplit]
  rcases Nat.lt_or_ge ⌊R ^ 2⌋₊ 2 with ht | ht
  · -- at `t ≤ 1` the Green kernel is the identity and the square sum is at most one
    have hsmall : (∑' z : Sandpile.Site d, Sandpile.greenTime d ⌊R ^ 2⌋₊ 0 z ^ 2) ≤ 1 := by
      interval_cases h : ⌊R ^ 2⌋₊
      · simp [Sandpile.greenTime, LatticeProb.greenTime]
      · have hg : ∀ z : Sandpile.Site d,
            Sandpile.greenTime d 1 0 z ^ 2 = if z = 0 then (1 : ℝ) else 0 := by
          intro z
          by_cases hz : z = 0 <;>
            simp [Sandpile.greenTime, LatticeProb.greenTime,
              LatticeProb.LocalCLT.heatKernel, hz, eq_comm]
        rw [tsum_congr hg, tsum_ite_eq]
    have hnn : (0 : ℝ) ≤ ∑' z : Sandpile.Site d, Sandpile.greenTime d ⌊R ^ 2⌋₊ 0 z ^ 2 :=
      tsum_nonneg fun z => sq_nonneg _
    have hle : a ≤ 1 := rescale_factor_le_one d hd3 R hR
    have hpos : 0 < a := rescale_factor_pos d R hR0
    have : a ^ 2 * (∑' z : Sandpile.Site d, Sandpile.greenTime d ⌊R ^ 2⌋₊ 0 z ^ 2) ≤ 1 := by
      nlinarith
    exact le_trans this (le_max_right _ _)
  · have hbound := (hQ ⌊R ^ 2⌋₊ ht).2
    rw [varianceRate_eq_rpow d hd hd3] at hbound
    exact le_trans (scaled_sq_bound d hd3 C hC.le R hR _ hbound) (le_max_left _ _)

/-- The square Green sum is a finite sum, hence summable. -/
theorem summable_greenTime_sq (t : ℕ) (x : Sandpile.Site d) :
    Summable fun z : Sandpile.Site d => Sandpile.greenTime d t x z ^ 2 := by
  refine summable_of_ne_finset_zero (s := Sandpile.boxFinset x t) fun z hz => ?_
  have hg : Sandpile.greenTime d t x z = 0 := by
    by_contra hne
    exact hz (Sandpile.mem_boxFinset (Sandpile.greenTime_support t x hne))
  simp [hg]

/-- **Both Green norms at the parabolic scale are bounded uniformly in `R`.**
The two displays of `sandpile.tex:2003-2006`: the square sum of the weights
`R^{-(2-d/2)}g_{⌊R²⌋}(0,z)` and their supremum are bounded by one constant. -/
theorem exists_scaled_greenTime_norm_bounds (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ R : ℝ, 1 ≤ R →
      (∑' z : Sandpile.Site d,
          (R ^ (-(2 - (d : ℝ) / 2)) * Sandpile.greenTime d ⌊R ^ 2⌋₊ 0 z) ^ 2) ≤ M ∧
        ∀ z : Sandpile.Site d,
          R ^ (-(2 - (d : ℝ) / 2)) * Sandpile.greenTime d ⌊R ^ 2⌋₊ 0 z ≤ M := by
  obtain ⟨M, hM1, hM⟩ := exists_scaled_greenTime_sq_bound d hd hd3
  refine ⟨M, hM1, fun R hR => ⟨hM R hR, fun z => ?_⟩⟩
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR
  set a : ℝ := R ^ (-(2 - (d : ℝ) / 2)) with ha
  have hanneg : 0 ≤ a := (rescale_factor_pos d R hR0).le
  have hgnn : 0 ≤ Sandpile.greenTime d ⌊R ^ 2⌋₊ 0 z := Sandpile.greenTime_nonneg _ _ _
  have hsum : Summable fun w : Sandpile.Site d =>
      (a * Sandpile.greenTime d ⌊R ^ 2⌋₊ 0 w) ^ 2 :=
    ((summable_greenTime_sq ⌊R ^ 2⌋₊ (0 : Sandpile.Site d)).mul_left (a ^ 2)).congr
      fun w => by ring
  have hterm : (a * Sandpile.greenTime d ⌊R ^ 2⌋₊ 0 z) ^ 2
      ≤ ∑' w : Sandpile.Site d, (a * Sandpile.greenTime d ⌊R ^ 2⌋₊ 0 w) ^ 2 := by
    have := hsum.sum_le_tsum ({z} : Finset (Sandpile.Site d)) fun w _ => sq_nonneg _
    simpa using this
  have hsq : (a * Sandpile.greenTime d ⌊R ^ 2⌋₊ 0 z) ^ 2 ≤ M := le_trans hterm (hM R hR)
  nlinarith [mul_nonneg hanneg hgnn]

end Sandpile.Support
