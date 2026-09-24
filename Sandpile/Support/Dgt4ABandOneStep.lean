/-
The Taylor step of the one-step profile of Step 2 of `thm:dgt4-many-limits`
(`eq:dgt4-band-one-step-profile`, `sandpile.tex:6201-6217`).

The paper's sentence is "Taylor's formula gives the second line because the
relative change in `z_{k,n}` is `O(ω_k z_{k,n}^{ϑ_k}) = o(1)`": the mean
increment `E u_{n+1}(0) - E u_n(0)` decreases `z_{k,n}` by
`ω_k z_{k,n}^{ϑ_k+1}/(G(0,0)(ϑ_k+1))` to leading order, and the reciprocal power
`y_{k,n} = z_{k,n}^{-ϑ_k}` therefore increases by `ω_k/(G(0,0)κ_k)` to leading
order, with `κ_k = 1 + 1/ϑ_k`.

Nothing here is probabilistic: it is the real-analytic identity that turns the
integrated profile into the constant increments that
`scaledProfile_of_increments` sums.  Both directions come from Bernoulli's
inequality for real exponents, applied to `(1-u)^{-ϑ}` once through
`(1-u)^{-1} = 1 + u/(1-u)` and once through `1 - ϑu ≤ (1-u)^{ϑ}`.
-/
import Mathlib

open Filter Topology

noncomputable section

namespace Sandpile.Support

/-- **Bernoulli's inequality sandwiches `(1-u)^{-ϑ}` between `1 + ϑu` and
`(1-ϑu)⁻¹`**, so its Taylor error at first order is quadratic. -/
theorem abs_rpow_neg_one_sub_le {θ u : ℝ} (hθ1 : 1 ≤ θ) (hθ2 : θ ≤ 2)
    (hu0 : 0 ≤ u) (hu : θ * u ≤ 1 / 2) :
    |(1 - u) ^ (-θ) - 1 - θ * u| ≤ 8 * u ^ 2 := by
  have hθ0 : (0 : ℝ) < θ := lt_of_lt_of_le zero_lt_one hθ1
  have hθu : 0 ≤ θ * u := mul_nonneg hθ0.le hu0
  have hu2 : u ≤ 1 / 2 := by nlinarith
  have hpos : (0 : ℝ) < 1 - u := by linarith
  have hθupos : (0 : ℝ) < 1 - θ * u := by linarith
  have hrp : (0 : ℝ) < (1 - u) ^ θ := Real.rpow_pos_of_pos hpos θ
  have hneg : (1 - u) ^ (-θ) = ((1 - u) ^ θ)⁻¹ := Real.rpow_neg hpos.le θ
  -- the lower bound, from Bernoulli applied to `1 + u/(1-u)`
  have hlow : 1 + θ * u ≤ (1 - u) ^ (-θ) := by
    have hs : (-1 : ℝ) ≤ u / (1 - u) := le_trans (by norm_num) (div_nonneg hu0 hpos.le)
    have hbern := one_add_mul_self_le_rpow_one_add hs hθ1
    have hbase : 1 + u / (1 - u) = (1 - u)⁻¹ := by
      field_simp
      ring
    rw [hbase, Real.inv_rpow hpos.le, ← hneg] at hbern
    refine le_trans ?_ hbern
    have h1 : u ≤ u / (1 - u) := by
      rw [le_div_iff₀ hpos]
      nlinarith
    nlinarith
  -- the upper bound, from Bernoulli applied to `1 - u`
  have hhigh : (1 - u) ^ (-θ) ≤ (1 - θ * u)⁻¹ := by
    have hs : (-1 : ℝ) ≤ -u := by linarith
    have hbern := one_add_mul_self_le_rpow_one_add hs hθ1
    have hbase : (1 : ℝ) + -u = 1 - u := by ring
    have hlin : (1 : ℝ) + θ * -u = 1 - θ * u := by ring
    rw [hbase, hlin] at hbern
    rw [hneg]
    exact inv_anti₀ hθupos hbern
  -- the gap between the two bounds is quadratic
  have hgap : (1 - θ * u)⁻¹ - 1 - θ * u ≤ 8 * u ^ 2 := by
    have hid : (1 - θ * u)⁻¹ - 1 - θ * u = (θ * u) ^ 2 / (1 - θ * u) := by
      field_simp
      ring
    rw [hid, div_le_iff₀ hθupos]
    have hfac : 0 ≤ 8 - 8 * (θ * u) - θ ^ 2 := by nlinarith
    nlinarith [mul_nonneg (sq_nonneg u) hfac]
  rw [abs_le]
  constructor
  · linarith
  · linarith

/-- **The one-step increment of the reciprocal power**
(`eq:dgt4-band-one-step-profile`).  If the decrement `δ` of `z` is
`c z^{ϑ+1}` up to the relative error `ε`, then `z^{-ϑ}` increases by `ϑ c` up to
`ϑ c ε` plus a term of order `c²`. -/
theorem abs_oneStep_increment_le {θ c z δ ε : ℝ}
    (hθ1 : 1 ≤ θ) (hθ2 : θ ≤ 2) (hz0 : 0 < z) (hc : 0 < c) (hε : 0 ≤ ε)
    (hδ0 : 0 ≤ δ) (hδ : |δ - c * z ^ (θ + 1)| ≤ ε * (c * z ^ (θ + 1)))
    (hsmall : θ * (δ / z) ≤ 1 / 2) :
    |(z - δ) ^ (-θ) - z ^ (-θ) - θ * c|
      ≤ θ * c * ε + 8 * (1 + ε) ^ 2 * c ^ 2 * z ^ θ := by
  have hθ0 : (0 : ℝ) < θ := lt_of_lt_of_le zero_lt_one hθ1
  set u : ℝ := δ / z with hudef
  have hu0 : 0 ≤ u := div_nonneg hδ0 hz0.le
  have hzu : z * u = δ := by
    rw [hudef]
    field_simp
  have hu2 : u ≤ 1 / 2 := by nlinarith
  have hpos : (0 : ℝ) < 1 - u := by linarith
  -- the two powers of `z`
  set Z : ℝ := z ^ θ with hZ
  set Y : ℝ := z ^ (-θ) with hY
  have hZpos : 0 < Z := Real.rpow_pos_of_pos hz0 θ
  have hYpos : 0 < Y := Real.rpow_pos_of_pos hz0 (-θ)
  have hZY : Z * Y = 1 := by
    rw [hZ, hY, ← Real.rpow_add hz0]
    simp
  have hzz : z ^ (θ + 1) = Z * z := by
    rw [hZ, Real.rpow_add hz0, Real.rpow_one]
  -- factor the shifted power
  have hfac : (z - δ) ^ (-θ) = Y * (1 - u) ^ (-θ) := by
    have hrw : z - δ = z * (1 - u) := by rw [← hzu]; ring
    rw [hrw, Real.mul_rpow hz0.le hpos.le, hY]
  -- the Taylor bound on the rescaled factor
  have hkey := abs_rpow_neg_one_sub_le hθ1 hθ2 hu0 hsmall
  -- the size of the decrement
  have hδle : δ ≤ (1 + ε) * (c * (Z * z)) := by
    have h1 : δ - c * z ^ (θ + 1) ≤ ε * (c * z ^ (θ + 1)) := (abs_le.mp hδ).2
    rw [hzz] at h1
    nlinarith
  have hule : u ≤ (1 + ε) * (c * Z) := by
    rw [hudef, div_le_iff₀ hz0]
    nlinarith
  -- the leading term
  have hlead : |Y * (θ * u) - θ * c| ≤ θ * c * ε := by
    have hrw : Y * (θ * u) - θ * c = (θ * (Y / z)) * (δ - c * (Z * z)) := by
      rw [← hzu]
      field_simp
      nlinarith [hZY]
    rw [hrw, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ θ * (Y / z))]
    have h1 : |δ - c * (Z * z)| ≤ ε * (c * (Z * z)) := by rw [← hzz]; exact hδ
    have h2 : θ * (Y / z) * |δ - c * (Z * z)| ≤ θ * (Y / z) * (ε * (c * (Z * z))) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    refine h2.trans (le_of_eq ?_)
    field_simp
    nlinarith [hZY]
  -- the quadratic term
  have hquad : Y * (8 * u ^ 2) ≤ 8 * (1 + ε) ^ 2 * c ^ 2 * z ^ θ := by
    have hsq : u ^ 2 ≤ ((1 + ε) * (c * Z)) ^ 2 := by nlinarith
    have h1 : Y * (8 * u ^ 2) ≤ Y * (8 * ((1 + ε) * (c * Z)) ^ 2) := by nlinarith
    refine h1.trans (le_of_eq ?_)
    rw [← hZ]
    nlinarith [hZY]
  -- assemble
  have hsplit : (z - δ) ^ (-θ) - Y - θ * c
      = Y * ((1 - u) ^ (-θ) - 1 - θ * u) + (Y * (θ * u) - θ * c) := by
    rw [hfac]; ring
  have hb1 : |Y * ((1 - u) ^ (-θ) - 1 - θ * u)| ≤ Y * (8 * u ^ 2) := by
    rw [abs_mul, abs_of_pos hYpos]
    exact mul_le_mul_of_nonneg_left hkey hYpos.le
  calc |(z - δ) ^ (-θ) - z ^ (-θ) - θ * c|
      = |Y * ((1 - u) ^ (-θ) - 1 - θ * u) + (Y * (θ * u) - θ * c)| := by rw [← hY, ← hsplit]
    _ ≤ |Y * ((1 - u) ^ (-θ) - 1 - θ * u)| + |Y * (θ * u) - θ * c| := abs_add_le _ _
    _ ≤ Y * (8 * u ^ 2) + θ * c * ε := add_le_add hb1 hlead
    _ ≤ 8 * (1 + ε) ^ 2 * c ^ 2 * z ^ θ + θ * c * ε := by linarith
    _ = θ * c * ε + 8 * (1 + ε) ^ 2 * c ^ 2 * z ^ θ := by ring

/-- The paper's constant: `ϑ` times the coefficient `ω/(G(0,0)(ϑ+1))` of the
one-step decrement is `ω/(G(0,0)κ)` with `κ = 1 + 1/ϑ`. -/
theorem theta_mul_coeff_eq {ω G θ : ℝ} (hG : G ≠ 0) (hθ : 0 < θ) :
    θ * (ω / (G * (θ + 1))) = ω / (G * (1 + 1 / θ)) := by
  have h1 : θ + 1 ≠ 0 := by positivity
  field_simp

/-- **The one-step increment in the shape the summation consumes**
(`eq:dgt4-band-one-step-profile`): with the decrement of `z` equal to
`ω z^{ϑ+1}/(G(0,0)(ϑ+1))` up to the relative error `ε`, the increment of
`z^{-ϑ}` is `ω/(G(0,0)κ)` up to `η ω` with `η = ε/G(0,0) + 8(1+ε)²ω/G(0,0)²`. -/
theorem abs_oneStep_increment_le' {θ ω G z δ ε : ℝ}
    (hθ1 : 1 ≤ θ) (hθ2 : θ ≤ 2) (hz0 : 0 < z) (hz1 : z ≤ 1) (hG : 0 < G) (hω : 0 < ω)
    (hε : 0 ≤ ε) (hδ0 : 0 ≤ δ)
    (hδ : |δ - ω / (G * (θ + 1)) * z ^ (θ + 1)| ≤ ε * (ω / (G * (θ + 1)) * z ^ (θ + 1)))
    (hsmall : θ * (δ / z) ≤ 1 / 2) :
    |(z - δ) ^ (-θ) - z ^ (-θ) - ω / (G * (1 + 1 / θ))|
      ≤ (ε / G + 8 * (1 + ε) ^ 2 * ω / G ^ 2) * ω := by
  have hθ0 : (0 : ℝ) < θ := lt_of_lt_of_le zero_lt_one hθ1
  have hden : (0 : ℝ) < G * (θ + 1) := by positivity
  have hcpos : 0 < ω / (G * (θ + 1)) := div_pos hω hden
  have hmain := abs_oneStep_increment_le hθ1 hθ2 hz0 hcpos hε hδ0 hδ hsmall
  rw [theta_mul_coeff_eq (ne_of_gt hG) hθ0] at hmain
  have hzθ : z ^ θ ≤ 1 := Real.rpow_le_one hz0.le hz1 hθ0.le
  have hzθ0 : (0 : ℝ) ≤ z ^ θ := (Real.rpow_pos_of_pos hz0 θ).le
  -- the leading term
  have hGle : G ≤ G * (1 + 1 / θ) := by
    have hinv : (0 : ℝ) < 1 / θ := by positivity
    nlinarith
  have hlead : ω / (G * (1 + 1 / θ)) * ε ≤ ε / G * ω := by
    have h1 : ω / (G * (1 + 1 / θ)) ≤ ω / G :=
      div_le_div_of_nonneg_left hω.le hG hGle
    calc ω / (G * (1 + 1 / θ)) * ε ≤ ω / G * ε := mul_le_mul_of_nonneg_right h1 hε
      _ = ε / G * ω := by ring
  -- the quadratic term
  have hcG : ω / (G * (θ + 1)) ≤ ω / G := by
    refine div_le_div_of_nonneg_left hω.le hG ?_
    nlinarith
  have hquad : 8 * (1 + ε) ^ 2 * (ω / (G * (θ + 1))) ^ 2 * z ^ θ
      ≤ 8 * (1 + ε) ^ 2 * ω / G ^ 2 * ω := by
    have hA : (0 : ℝ) ≤ 8 * (1 + ε) ^ 2 * (ω / (G * (θ + 1))) ^ 2 := by positivity
    have hsq : (ω / (G * (θ + 1))) ^ 2 ≤ (ω / G) ^ 2 := by
      have := hcpos.le
      nlinarith
    calc 8 * (1 + ε) ^ 2 * (ω / (G * (θ + 1))) ^ 2 * z ^ θ
        ≤ 8 * (1 + ε) ^ 2 * (ω / (G * (θ + 1))) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hzθ hA
      _ = 8 * (1 + ε) ^ 2 * (ω / (G * (θ + 1))) ^ 2 := mul_one _
      _ ≤ 8 * (1 + ε) ^ 2 * (ω / G) ^ 2 := by nlinarith [sq_nonneg (1 + ε)]
      _ = 8 * (1 + ε) ^ 2 * ω / G ^ 2 * ω := by
          rw [div_pow]
          ring
  linarith

end Sandpile.Support
