/-
**The good event of Step 3** (`eq:dgt4-gaussian-positive-off-origin`,
`sandpile.tex:5184-5197`): the conditional probability that the field `V_\infty+\E u_n(0)`
fails to be positive somewhere on the punctured box of radius `k_n+1` tends to zero,

  `Ck_n^d\exp\{-c(\E u_n(0))^2\}\longrightarrow0` .

`measure_resid_exists_nonpos_le` is the union bound with the explicit constant.  What is
added here is the arithmetic that its right-hand side vanishes: the box has
`(2k+1)^d` sites, the horizon `k_n` is a power of `\log(n+2)`, and the height is at least
`c\sqrt{\log n}` by `exists_sqrt_log_le_meanOdometer`, so the bound is a power of a
logarithm against a power of `n`, and `isLittleO_log_rpow_rpow_atTop` settles it.
-/
import Sandpile.Support.Dgt4AHeightOrder
import Sandpile.Support.Dgt4ACondTail
import Sandpile.Support.IncrementBall
import Sandpile.Support.Dgt4AStep2LipHorizon

open MeasureTheory ProbabilityTheory Filter Topology Set Asymptotics
open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}

/-- A power of a logarithm is beaten by every negative power of `n`. -/
theorem tendsto_log_rpow_mul_rpow_neg {p b : ℝ} (hb : 0 < b) :
    Tendsto (fun n : ℕ => (Real.log n) ^ p * (n : ℝ) ^ (-b)) atTop (𝓝 0) := by
  have hlit : (fun x : ℝ => (Real.log x) ^ p) =o[atTop] fun x : ℝ => x ^ b :=
    isLittleO_log_rpow_rpow_atTop p hb
  have hdiv : Tendsto (fun x : ℝ => (Real.log x) ^ p / x ^ b) atTop (𝓝 0) :=
    hlit.tendsto_div_nhds_zero
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hcomp : Tendsto (fun n : ℕ => (Real.log (n : ℝ)) ^ p / (n : ℝ) ^ b) atTop (𝓝 0) :=
    hdiv.comp hnat
  refine hcomp.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [Real.rpow_neg hnR.le, div_eq_mul_inv]

/-- The punctured box at the horizon has at most a power of `\log n` sites. -/
theorem exists_boxCard_horizon_le (hd : 5 ≤ d) :
    ∃ C p : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ((boxFinset (0 : Site d) (dgt4Horizon d n + 1)).card : ℝ) ≤ C * (Real.log n) ^ p := by
  have hdR : (5 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  set q : ℝ := 6 / ((d : ℝ) - 4) with hq
  have hqpos : 0 < q := by
    rw [hq]
    apply div_pos (by norm_num)
    linarith
  refine ⟨(7 : ℝ) ^ d * (2 : ℝ) ^ (q * d), q * d, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop 3] with n hn3
  have hn2R : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  set L : ℝ := Real.log ((n : ℝ) + 2) with hL
  have hLge : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hlogn : 1 ≤ Real.log (n : ℝ) := by
    rw [Real.le_log_iff_exp_le hnpos]
    have := Real.exp_one_lt_d9
    linarith
  have hLle : L ≤ 2 * Real.log (n : ℝ) := by
    have hsq : (n : ℝ) + 2 ≤ (n : ℝ) ^ 2 := by nlinarith
    have h1 : L ≤ Real.log ((n : ℝ) ^ 2) :=
      Real.log_le_log (by linarith) hsq
    rwa [Real.log_pow, Nat.cast_ofNat] at h1
  have hLq : 1 ≤ L ^ q := Real.one_le_rpow hLge hqpos.le
  have hceil : ((dgt4Horizon d n : ℕ) : ℝ) ≤ L ^ q + 1 := by
    rw [dgt4Horizon]
    exact le_of_lt (Nat.ceil_lt_add_one (by positivity))
  have hcard : ((boxFinset (0 : Site d) (dgt4Horizon d n + 1)).card : ℝ)
      = ((2 * (dgt4Horizon d n + 1) + 1 : ℕ) : ℝ) ^ d := by
    rw [card_boxFinset]
    push_cast
    ring
  have hbase : ((2 * (dgt4Horizon d n + 1) + 1 : ℕ) : ℝ) ≤ 7 * L ^ q := by
    push_cast
    linarith
  have hbnn : (0 : ℝ) ≤ ((2 * (dgt4Horizon d n + 1) + 1 : ℕ) : ℝ) := by positivity
  have hpow : ((2 * (dgt4Horizon d n + 1) + 1 : ℕ) : ℝ) ^ d ≤ (7 * L ^ q) ^ d :=
    pow_le_pow_left₀ hbnn hbase d
  have hexpand : (7 * L ^ q) ^ d = (7 : ℝ) ^ d * (L ^ (q * d)) := by
    rw [mul_pow, ← Real.rpow_natCast (L ^ q) d, ← Real.rpow_mul (by linarith : (0:ℝ) ≤ L)]
  have hLpow : L ^ (q * d) ≤ (2 : ℝ) ^ (q * d) * (Real.log (n : ℝ)) ^ (q * d) := by
    have h1 : L ^ (q * d) ≤ (2 * Real.log (n : ℝ)) ^ (q * d) :=
      Real.rpow_le_rpow (by linarith) hLle (by positivity)
    rwa [Real.mul_rpow (by norm_num) (by linarith)] at h1
  calc ((boxFinset (0 : Site d) (dgt4Horizon d n + 1)).card : ℝ)
      = ((2 * (dgt4Horizon d n + 1) + 1 : ℕ) : ℝ) ^ d := hcard
    _ ≤ (7 * L ^ q) ^ d := hpow
    _ = (7 : ℝ) ^ d * (L ^ (q * d)) := hexpand
    _ ≤ (7 : ℝ) ^ d * ((2 : ℝ) ^ (q * d) * (Real.log (n : ℝ)) ^ (q * d)) := by
        exact mul_le_mul_of_nonneg_left hLpow (by positivity)
    _ = (7 : ℝ) ^ d * (2 : ℝ) ^ (q * d) * (Real.log (n : ℝ)) ^ (q * d) := by ring

/-- **The right-hand side of `eq:dgt4-gaussian-positive-off-origin` vanishes**
(`sandpile.tex:5187-5192`): `Ck_n^d\exp\{-c(\E u_n(0))^2\}\to0`. -/
theorem tendsto_boxCard_mul_exp_neg_sq
    (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d) (v : ℝ≥0) (hv : v ≠ 0)
    {b : ℝ} (hb : 0 < b) :
    Tendsto (fun n : ℕ =>
        ((boxFinset (0 : Site d) (dgt4Horizon d n + 1)).card : ℝ) *
          (2 * Real.exp (-(b * (meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n) ^ 2))))
      atTop (𝓝 0) := by
  obtain ⟨c₀, hc₀, hlow⟩ := exists_sqrt_log_le_meanOdometer hGH hd v hv
  obtain ⟨C, p, hC, hcard⟩ := exists_boxCard_horizon_le (d := d) hd
  have hbc : 0 < b * c₀ ^ 2 := by positivity
  have hmaj : Tendsto
      (fun n : ℕ => 2 * C * ((Real.log (n : ℝ)) ^ p * (n : ℝ) ^ (-(b * c₀ ^ 2))))
      atTop (𝓝 0) := by
    have h := (tendsto_log_rpow_mul_rpow_neg (p := p) (b := b * c₀ ^ 2) hbc).const_mul (2 * C)
    simpa using h
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards with n
    positivity
  · filter_upwards [hcard, hlow, eventually_ge_atTop 3] with n hc hl hn3
    have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
    have hlogn0 : (0 : ℝ) ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
    have hsq : c₀ ^ 2 * Real.log (n : ℝ)
        ≤ (meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n) ^ 2 := by
      have hs := Real.sq_sqrt hlogn0
      have hnn : (0 : ℝ) ≤ c₀ * Real.sqrt (Real.log (n : ℝ)) := by positivity
      have hsq2 : (c₀ * Real.sqrt (Real.log (n : ℝ))) ^ 2
          ≤ (meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n) ^ 2 :=
        pow_le_pow_left₀ hnn hl 2
      have hid : (c₀ * Real.sqrt (Real.log (n : ℝ))) ^ 2 = c₀ ^ 2 * Real.log (n : ℝ) := by
        rw [mul_pow, hs]
      linarith
    have hexp : Real.exp (-(b * (meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n) ^ 2))
        ≤ (n : ℝ) ^ (-(b * c₀ ^ 2)) := by
      rw [Real.rpow_def_of_pos (by linarith : (0 : ℝ) < (n : ℝ))]
      refine Real.exp_le_exp.2 ?_
      nlinarith [hsq, hb]
    have hrhs : (0 : ℝ) ≤ C * (Real.log (n : ℝ)) ^ p :=
      mul_nonneg hC.le (Real.rpow_nonneg hlogn0 p)
    calc ((boxFinset (0 : Site d) (dgt4Horizon d n + 1)).card : ℝ) *
          (2 * Real.exp (-(b * (meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n) ^ 2)))
        ≤ (C * (Real.log (n : ℝ)) ^ p) * (2 * (n : ℝ) ^ (-(b * c₀ ^ 2))) := by
          refine mul_le_mul hc (by linarith) (by positivity) hrhs
      _ = 2 * C * ((Real.log (n : ℝ)) ^ p * (n : ℝ) ^ (-(b * c₀ ^ 2))) := by ring

end Sandpile
