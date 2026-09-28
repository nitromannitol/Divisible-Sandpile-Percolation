import Sandpile.Support.CorrelationRow
import Sandpile.Support.GeomRow
import Sandpile.Support.GreenSup

/-!
# The rates at the geometric scales

The rates at the geometric scales.

The third-moment estimate of `sandpile.tex:1784-1790` needs the supremum of the Green kernel
divided by its own standard deviation, `S(n)/n^{(4-d)/4}`, summed over the scales `n_j = N q^j`.
That quantity decays geometrically with ratio `q^{-1/4}` in every dimension one to three, so its
sum is at most six times its first term. In dimension two the extra logarithm is absorbed by the
same inequality `1 + l log q ≤ 3 q^{l/4}` that carries the correlation bound.
-/

namespace Sandpile

variable {d : ℕ}


variable {d : ℕ}

/-- In dimensions one to three the variance rate of `eq:Qt-table` is the power
`t^{(4-d)/2}`. -/
theorem varianceRate_eq_rpow (hd : 1 ≤ d) (hd3 : d ≤ 3) (t : ℕ) :
    Sandpile.External.Variance.varianceRate d t = (t : ℝ) ^ (((4 : ℝ) - (d : ℝ)) / 2) := by
  interval_cases d
  · norm_num [Sandpile.External.Variance.varianceRate]
  · norm_num [Sandpile.External.Variance.varianceRate]
  · norm_num [Sandpile.External.Variance.varianceRate]

/-- The rate of the third-moment estimate: the supremum of the Green kernel
divided by its own standard deviation. -/
noncomputable def supOverSd (d n : ℕ) : ℝ :=
  greenSupRate d n / (n : ℝ) ^ (((4 : ℝ) - (d : ℝ)) / 4)

/-- `supOverSd d n` is nonnegative, being a ratio of nonnegative quantities (`greenSupRate` over
a nonnegative power). -/
theorem supOverSd_nonneg (d n : ℕ) : 0 ≤ supOverSd d n := by
  rw [supOverSd]
  exact div_nonneg (greenSupRate_nonneg d n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)


variable {d : ℕ}

/-- The lattice power at a geometric scale. -/
theorem rpow_geom_scale {q N : ℕ} (hq : 1 ≤ q) (hN : 1 ≤ N) (j : ℕ) (α : ℝ) :
    ((N * q ^ j : ℕ) : ℝ) ^ α = (N : ℝ) ^ α * ((q : ℝ) ^ α) ^ j := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  push_cast
  rw [Real.mul_rpow hN0.le (by positivity)]
  congr 1
  rw [← Real.rpow_natCast (q : ℝ) j, ← Real.rpow_mul hq0.le,
    ← Real.rpow_natCast ((q : ℝ) ^ α) j, ← Real.rpow_mul hq0.le]
  congr 1
  ring



variable {d : ℕ}

/-- The square root commutes with a natural-number power: `sqrt (x ^ j) = sqrt x ^ j`, proved
by induction on `j` using `Real.sqrt_mul`. -/
theorem sqrt_pow_nat {x : ℝ} (hx : 0 ≤ x) (j : ℕ) :
    Real.sqrt (x ^ j) = Real.sqrt x ^ j := by
  induction j with
  | zero => simp
  | succ n ih => rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]

/-- At the geometric scale `N q^j`, the Green-kernel supremum rate `greenSupRate d (N q^j)` is at
most `3 * greenSupRate d N * (q ^ ((4-d)/4 - 1/4))^j`, verified case by case in dimensions one to
three: an exact identity in dimension one and three, and the logarithmic inequality
`1 + l log q ≤ 3 q^{l/4}` (`one_add_mul_log_le`) absorbing the extra term in dimension two. -/
theorem greenSupRate_geom_le (hd : 1 ≤ d) (hd3 : d ≤ 3) {q N : ℕ} (hq : 1 ≤ q) (hN : 1 ≤ N)
    (j : ℕ) :
    greenSupRate d (N * q ^ j)
      ≤ 3 * greenSupRate d N * (((q : ℝ) ^ ((((4 : ℝ) - (d : ℝ)) / 4) - 1 / 4)) ^ j) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  interval_cases d
  · -- dimension one: the exponent is 1/2 and the bound is an identity times three
    have hexp : (((4 : ℝ) - ((1 : ℕ) : ℝ)) / 4) - 1 / 4 = (1 : ℝ) / 2 := by norm_num
    rw [hexp]
    have hsqrt : ((q : ℝ) ^ ((1 : ℝ) / 2)) = Real.sqrt (q : ℝ) :=
      (Real.sqrt_eq_rpow (q : ℝ)).symm
    have hleft : greenSupRate 1 (N * q ^ j) = Real.sqrt (N : ℝ) * Real.sqrt (q : ℝ) ^ j := by
      rw [greenSupRate, if_pos rfl]
      push_cast
      rw [Real.sqrt_mul hN0.le, sqrt_pow_nat hq0.le j]
    have hright : greenSupRate 1 N = Real.sqrt (N : ℝ) := by
      rw [greenSupRate, if_pos rfl]
    rw [hleft, hright, hsqrt]
    have h1 : (0 : ℝ) ≤ Real.sqrt (N : ℝ) * Real.sqrt (q : ℝ) ^ j := by positivity
    linarith
  · -- dimension two: the logarithm splits and the extra factor is absorbed
    have hexp : (((4 : ℝ) - ((2 : ℕ) : ℝ)) / 4) - 1 / 4 = (1 : ℝ) / 4 := by norm_num
    rw [hexp]
    have hleft : greenSupRate 2 (N * q ^ j)
        = 1 + (Real.log (N : ℝ) + (j : ℝ) * Real.log (q : ℝ)) := by
      rw [greenSupRate]
      norm_num
      rw [Real.log_mul (ne_of_gt hN0) (by positivity), Real.log_pow]
    have hright : greenSupRate 2 N = 1 + Real.log (N : ℝ) := by
      rw [greenSupRate]; norm_num
    have hlogN : (0 : ℝ) ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
    have hlogq : (0 : ℝ) ≤ (j : ℝ) * Real.log (q : ℝ) := by
      have := Real.log_natCast_nonneg q
      positivity
    have hpow : (((q : ℝ) ^ ((1 : ℝ) / 4)) ^ j) = (q : ℝ) ^ ((j : ℝ) / 4) := by
      rw [rpow_pow_eq hq0]
      congr 1
      ring
    rw [hleft, hright, hpow]
    have hbound := one_add_mul_log_le hq j
    nlinarith [hbound, hlogN, hlogq]
  · -- dimension three: the exponent is zero
    have hexp : (((4 : ℝ) - ((3 : ℕ) : ℝ)) / 4) - 1 / 4 = (0 : ℝ) := by norm_num
    rw [hexp]
    have hleft : greenSupRate 3 (N * q ^ j) = 1 := by norm_num [greenSupRate]
    have hright : greenSupRate 3 N = 1 := by norm_num [greenSupRate]
    rw [hleft, hright, Real.rpow_zero, one_pow]
    norm_num



variable {d : ℕ}

/-- The third-moment rate `supOverSd d (N q^j)` at the geometric scale `N q^j` is at most
`3 * supOverSd d N * (geomRatio q)^j`, dividing the numerator bound `greenSupRate_geom_le` by the
denominator identity `rpow_geom_scale` and simplifying the resulting power ratio to `geomRatio`. -/
theorem supOverSd_geom_le (hd : 1 ≤ d) (hd3 : d ≤ 3) {q N : ℕ} (hq : 1 ≤ q) (hN : 1 ≤ N)
    (j : ℕ) :
    supOverSd d (N * q ^ j) ≤ 3 * supOverSd d N * (geomRatio q) ^ j := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  set α : ℝ := ((4 : ℝ) - (d : ℝ)) / 4 with hα
  have hden : ((N * q ^ j : ℕ) : ℝ) ^ α = (N : ℝ) ^ α * ((q : ℝ) ^ α) ^ j :=
    rpow_geom_scale hq hN j α
  have hNα : (0 : ℝ) < (N : ℝ) ^ α := Real.rpow_pos_of_pos hN0 α
  have hqα : (0 : ℝ) < ((q : ℝ) ^ α) ^ j := pow_pos (Real.rpow_pos_of_pos hq0 α) j
  have hnum := greenSupRate_geom_le hd hd3 hq hN j
  have hratio : ((q : ℝ) ^ (α - 1 / 4)) ^ j / ((q : ℝ) ^ α) ^ j = (geomRatio q) ^ j := by
    rw [← div_pow, ← Real.rpow_sub hq0, geomRatio]
    congr 2
    ring
  rw [supOverSd, supOverSd, ← hα, hden]
  rw [div_le_iff₀ (by positivity)]
  have hsN : 0 ≤ greenSupRate d N := greenSupRate_nonneg d N
  have hfinal : 3 * (greenSupRate d N / (N : ℝ) ^ α) * (geomRatio q) ^ j *
      ((N : ℝ) ^ α * ((q : ℝ) ^ α) ^ j)
      = 3 * greenSupRate d N * (((q : ℝ) ^ (α - 1 / 4)) ^ j) := by
    field_simp
    rw [← hratio]
    field_simp
  rw [hfinal]
  exact hnum

/-- **Summing the third-moment rate over the geometric scales.** If the geometric ratio
`geomRatio q ≤ 1/2`, the sum `∑_{j<m} supOverSd d (N q^j)` is at most `6 * supOverSd d N`,
bounding each term by `supOverSd_geom_le` and summing the resulting geometric series
`∑ (geomRatio q)^j ≤ 2`. -/
theorem sum_supOverSd_geom_le (hd : 1 ≤ d) (hd3 : d ≤ 3) {q N : ℕ} (hq : 1 ≤ q) (hN : 1 ≤ N)
    (hr : geomRatio q ≤ 1 / 2) (m : ℕ) :
    ∑ j ∈ Finset.range m, supOverSd d (N * q ^ j) ≤ 6 * supOverSd d N := by
  have hgp : 0 < geomRatio q := geomRatio_pos hq
  have hs := supOverSd_nonneg d N
  have hbound : ∑ j ∈ Finset.range m, supOverSd d (N * q ^ j)
      ≤ ∑ j ∈ Finset.range m, 3 * supOverSd d N * (geomRatio q) ^ j :=
    Finset.sum_le_sum fun j _ => supOverSd_geom_le hd hd3 hq hN j
  have hgeom : ∑ j ∈ Finset.range m, (geomRatio q) ^ j ≤ 2 := by
    have h := geom_range_le hgp.le (by linarith : geomRatio q < 1) m
    have hinv : (1 - geomRatio q)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    linarith
  rw [← Finset.mul_sum] at hbound
  nlinarith [hbound, hgeom, hs]


end Sandpile
