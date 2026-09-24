/-
The integrated form of the deterministic chain of Step 2 of `lem:dgt4-path-survival`
(`sandpile.tex:5549-5567`).

`Support/LinProduct.lean` proves the chain POINTWISE in the path: the product
`∏_r (1-π_{R,r})^{I_{r,j}(X)}` is within `2 ∑_r I_{r,j}(X) π_{R,r}^2` of
`exp(-∑_r I_{r,j}(X) π_{R,r})`, and that exponential is within
`κ η + ε κ (η - log(1 - j/n_R))` of the profile `(1 - j/n_R)^κ` whenever the weighted
last-visit sum is within `η` of `-log(1 - j/n_R)`.  What
`lem:dgt4-weighted-last-visits` supplies is not a pointwise bound but an INTEGRAL one,
`∫_X |G(0,0) ∑_{i≤j} I_{i,j}(X)/(n_R-i) + log(1 - j/n_R)| dX ≤ η`, so the pointwise chain is
applied with the pointwise defect in place of `η` and then integrated; that is the single
lemma below.
-/
import Sandpile.Support.LinProduct

open MeasureTheory

namespace Sandpile

/-- **The integrated exponential comparison of Step 2.**  An INTEGRAL bound on the
last-visit defect `|G S + L|`, which is what `lem:dgt4-weighted-last-visits` supplies, gives
an integral bound on the deviation of `exp(-P)` from the profile `x ^ κ`. -/
theorem integral_abs_exp_neg_sub_rpow_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (κ G L η ε x : ℝ) (S P : Ω → ℝ)
    (hκ : 0 < κ) (hε : 0 ≤ ε) (hx : 0 < x) (hx1 : x ≤ 1) (hL : L = Real.log x)
    (hGS : ∀ ω, 0 ≤ G * S ω) (hP : ∀ ω, 0 ≤ P ω)
    (hPd : ∀ ω, |P ω - κ * (G * S ω)| ≤ ε * (κ * (G * S ω)))
    (hdiffint : Integrable (fun ω => |Real.exp (-P ω) - x ^ κ|) μ)
    (hSint : Integrable (fun ω => |G * S ω + L|) μ)
    (hη : ∫ ω, |G * S ω + L| ∂μ ≤ η) :
    ∫ ω, |Real.exp (-P ω) - x ^ κ| ∂μ ≤ κ * η + ε * κ * (η - L) := by
  have hpt : ∀ ω, |Real.exp (-P ω) - x ^ κ|
      ≤ (κ + ε * κ) * |G * S ω + L| - ε * κ * L := by
    intro ω
    have h := abs_exp_neg_sub_rpow_le κ G (S ω) L (|G * S ω + L|) ε (P ω) x hκ (hGS ω) hε
      hx hx1 hL le_rfl (hP ω) (hPd ω)
    calc |Real.exp (-P ω) - x ^ κ|
        ≤ κ * |G * S ω + L| + ε * κ * (|G * S ω + L| - L) := h
      _ = (κ + ε * κ) * |G * S ω + L| - ε * κ * L := by ring
  have hrhsint : Integrable (fun ω => (κ + ε * κ) * |G * S ω + L| - ε * κ * L) μ :=
    (hSint.const_mul (κ + ε * κ)).sub (integrable_const _)
  have hmono := integral_mono hdiffint hrhsint hpt
  have hval : ∫ ω, ((κ + ε * κ) * |G * S ω + L| - ε * κ * L) ∂μ
      = (κ + ε * κ) * (∫ ω, |G * S ω + L| ∂μ) - ε * κ * L := by
    rw [integral_sub (hSint.const_mul (κ + ε * κ)) (integrable_const _),
      integral_const_mul, integral_const, probReal_univ, smul_eq_mul, one_mul]
  rw [hval] at hmono
  have hcoef : 0 ≤ κ + ε * κ := by nlinarith
  nlinarith [hmono, hη, hcoef]

/-- **The profile is uniformly continuous on `[0,1]`.**  This is what replaces `n_R` by
`R² T` in `(1 - j/n_R)^κ` at the end of Step 2 of `lem:dgt4-path-survival`: since
`n_R/(R² T) → 1`, the two arguments differ by `o(1)` uniformly in `j`, and the profile is
uniformly continuous. -/
theorem exists_delta_rpow (κ : ℝ) (hκ : 0 ≤ κ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |x - y| < δ → |x ^ κ - y ^ κ| < ε := by
  have hcont : ContinuousOn (fun t : ℝ => t ^ κ) (Set.Icc (0 : ℝ) 1) :=
    (Real.continuous_rpow_const hκ).continuousOn
  have huc : UniformContinuousOn (fun t : ℝ => t ^ κ) (Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hcont
  obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
  refine ⟨δ, hδ, fun x hx y hy hxy => ?_⟩
  have := h x hx y hy (by rwa [Real.dist_eq])
  rwa [Real.dist_eq] at this

/-! ### The weight asymptotics of Step 2

`eq:dgt4-uniform-contact-thresholds` says that
`|m P(J(0) > E u_{m-1}(0))/(G(0,0)κ) - 1|` is eventually at most `η` uniformly for
`⌈ε n_R⌉ ≤ m ≤ n_R`.  With `m = n_R - r`, that is exactly the paper's substitution
`π_{R,r} = G(0,0)κ/(n_R-r)(1+o_R(1))` at `sandpile.tex:5558-5559`, in the two forms the
rest of Step 2 uses: a RELATIVE error against `G(0,0)κ/(n_R-r)`, which is what
`abs_sum_mul_sub_mul_sum_le` consumes, and a uniform UPPER bound `2G(0,0)κ/(n_R-r)`,
which is what `sum_inv_sq_range_le` needs to bound `∑_r π_{R,r}^2`. -/

/-- **The weight asymptotic, relative form.**  A relative error `eta` in `m π / (G κ)` is a
relative error `eta` in `π` against `G κ / m`. -/
theorem abs_weight_sub_le (m : ℕ) (hm : 0 < m) (Gk eta pi : ℝ) (hGk : 0 < Gk)
    (h : |(m : ℝ) * pi / Gk - 1| ≤ eta) :
    |pi - Gk / m| ≤ eta * (Gk / m) := by
  have hm' : (0:ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hc : (0:ℝ) < Gk / m := div_pos hGk hm'
  have hid : pi - Gk / m = (Gk / m) * ((m : ℝ) * pi / Gk - 1) := by
    field_simp
  rw [hid, abs_mul, abs_of_pos hc, mul_comm eta (Gk / m)]
  exact mul_le_mul_of_nonneg_left h (le_of_lt hc)

/-- **The weight asymptotic, uniform upper bound.**  A relative error at most one forces
`π ≤ 2 G κ / m`. -/
theorem weight_le_of_abs_le (m : ℕ) (hm : 0 < m) (Gk eta pi : ℝ) (hGk : 0 < Gk)
    (heta : eta ≤ 1) (h : |(m : ℝ) * pi / Gk - 1| ≤ eta) :
    pi ≤ 2 * Gk / m := by
  have hm' : (0:ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hub : (m : ℝ) * pi / Gk - 1 ≤ eta := (abs_le.mp h).2
  have h2 : (m : ℝ) * pi / Gk ≤ 2 := by linarith
  have h3 : (m : ℝ) * pi ≤ 2 * Gk := by
    rw [div_le_iff₀ hGk] at h2
    linarith
  rw [le_div_iff₀ hm']
  linarith

end Sandpile
