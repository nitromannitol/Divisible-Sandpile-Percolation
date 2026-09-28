import Sandpile.Support.Dgt4ThresholdChain

/-!
# From the mean-increment estimate to the reciprocal threshold chain

This file proves the passage, common to both cases of `prop:dgt4-contact-asymptotics`, from the
mean-increment estimate to the increments of the reciprocal threshold probability. Writing `b n`
for the threshold probability at `𝔼 u_n(0)`, `D n` for its decrement, `dl n` for the increment
of the mean odometer, `I n` for the integrated tail at `𝔼 u_n(0)`, `p n` for the density there
and `t n` for `𝔼 u_n(0)` itself, the chain assembles four factors each tending to one: the
mean-increment estimate `G dl n / I n → 1`, the two Mills ratios `t n I n / (v b n) → 1` and
`v p n / (t n b n) → 1`, and the first-order tail expansion `D n / (p n dl n) → 1`. Their product
with `G⁻¹` is `D n / (b n)^2`, the increment of the reciprocal `(b (n+1))⁻¹ - (b n)⁻¹` since
`b (n+1) = b n - D n`; the file also isolates the abstract Mills-ratio squeezes and the tail
expansion that feed the two case-specific proofs.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile

/-- If `b (n+1) = b n (1 - r n)` with `r n/b n → G⁻¹` and `r n → 0`, then the
increments of the reciprocal of `b` converge to `G⁻¹`. -/
theorem tendsto_inv_sub_inv_of_ratio {b r : ℕ → ℝ} {G : ℝ}
    (hbpos : ∀ n, 0 < b n)
    (hrec : ∀ n, b (n + 1) = b n * (1 - r n))
    (hr : Tendsto (fun n : ℕ => r n / b n) atTop (𝓝 G⁻¹))
    (hrz : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (b (n + 1))⁻¹ - (b n)⁻¹) atTop (𝓝 G⁻¹) := by
  have hone : Tendsto (fun n : ℕ => 1 - r n) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hrz
  have hinv : Tendsto (fun n : ℕ => (1 - r n)⁻¹) atTop (𝓝 1) := by
    simpa using hone.inv₀ one_ne_zero
  have hmul := hr.mul hinv
  rw [mul_one] at hmul
  refine hmul.congr' ?_
  have hne : ∀ᶠ n : ℕ in atTop, (1 : ℝ) - r n ≠ 0 :=
    hone.eventually_ne (by norm_num)
  filter_upwards [hne] with n hn
  have hb : b n ≠ 0 := (hbpos n).ne'
  rw [hrec n]
  field_simp
  ring

/-- The four factors of the chain multiply to the increment ratio `D n/(b n)^2`. -/
theorem tendsto_ratio_of_factors {b I p dl D t : ℕ → ℝ} {G v : ℝ} (hG : 0 < G) (hv : 0 < v)
    (hbpos : ∀ n, 0 < b n) (hIpos : ∀ᶠ n in atTop, 0 < I n) (hppos : ∀ᶠ n in atTop, 0 < p n)
    (htpos : ∀ᶠ n in atTop, 0 < t n) (hdl : ∀ᶠ n in atTop, 0 < dl n)
    (h1 : Tendsto (fun n : ℕ => G * dl n / I n) atTop (𝓝 1))
    (h2 : Tendsto (fun n : ℕ => t n * I n / (v * b n)) atTop (𝓝 1))
    (h3 : Tendsto (fun n : ℕ => v * p n / (t n * b n)) atTop (𝓝 1))
    (h4 : Tendsto (fun n : ℕ => D n / (p n * dl n)) atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => D n / (b n) ^ 2) atTop (𝓝 G⁻¹) := by
  have key : Tendsto (fun n : ℕ =>
      G⁻¹ * ((D n / (p n * dl n)) * ((v * p n / (t n * b n)) *
        ((G * dl n / I n) * (t n * I n / (v * b n)))))) atTop
      (𝓝 (G⁻¹ * (1 * (1 * (1 * 1))))) :=
    tendsto_const_nhds.mul (h4.mul (h3.mul (h1.mul h2)))
  rw [show G⁻¹ * (1 * (1 * (1 * 1))) = G⁻¹ by ring] at key
  refine key.congr' ?_
  filter_upwards [hdl, hIpos, hppos, htpos] with n hn hnI hnp hnt
  have hb : b n ≠ 0 := (hbpos n).ne'
  have hI : I n ≠ 0 := hnI.ne'
  have hp : p n ≠ 0 := hnp.ne'
  have ht : t n ≠ 0 := hnt.ne'
  have hd : dl n ≠ 0 := hn.ne'
  have hGne : G ≠ 0 := hG.ne'
  have hvne : v ≠ 0 := hv.ne'
  field_simp

/-- The chain: the four factors give the increments of the reciprocal threshold
probability. -/
theorem tendsto_inv_sub_inv_of_factors {b I p dl D t : ℕ → ℝ} {G v : ℝ} (hG : 0 < G) (hv : 0 < v)
    (hbpos : ∀ n, 0 < b n) (hIpos : ∀ᶠ n in atTop, 0 < I n) (hppos : ∀ᶠ n in atTop, 0 < p n)
    (htpos : ∀ᶠ n in atTop, 0 < t n) (hdl : ∀ᶠ n in atTop, 0 < dl n)
    (hbz : Tendsto b atTop (𝓝 0))
    (hD : ∀ n, b (n + 1) = b n - D n)
    (h1 : Tendsto (fun n : ℕ => G * dl n / I n) atTop (𝓝 1))
    (h2 : Tendsto (fun n : ℕ => t n * I n / (v * b n)) atTop (𝓝 1))
    (h3 : Tendsto (fun n : ℕ => v * p n / (t n * b n)) atTop (𝓝 1))
    (h4 : Tendsto (fun n : ℕ => D n / (p n * dl n)) atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => (b (n + 1))⁻¹ - (b n)⁻¹) atTop (𝓝 G⁻¹) := by
  have hratio := tendsto_ratio_of_factors hG hv hbpos hIpos hppos htpos hdl h1 h2 h3 h4
  refine tendsto_inv_sub_inv_of_ratio (r := fun n => D n / b n) hbpos ?_ ?_ ?_
  · intro n
    have hb : b n ≠ 0 := (hbpos n).ne'
    rw [hD n]
    field_simp
  · refine hratio.congr fun n => ?_
    have hb : b n ≠ 0 := (hbpos n).ne'
    field_simp
  · have hz := hratio.mul hbz
    rw [mul_zero] at hz
    refine hz.congr fun n => ?_
    have hb : b n ≠ 0 := (hbpos n).ne'
    field_simp

/-- `(1 + c/t^2)⁻¹ → 1`: the shape of both squeezing bounds below. -/
theorem tendsto_inv_one_add_div_sq (c : ℝ) :
    Tendsto (fun t : ℝ => (1 + c / t ^ 2)⁻¹) atTop (𝓝 1) := by
  have hsq : Tendsto (fun t : ℝ => t ^ 2) atTop atTop :=
    tendsto_pow_atTop (by norm_num)
  have hz : Tendsto (fun t : ℝ => c / t ^ 2) atTop (𝓝 0) :=
    hsq.const_div_atTop c
  have h1 : Tendsto (fun t : ℝ => 1 + c / t ^ 2) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hz
  simpa using h1.inv₀ (by norm_num)

/-- `(1 - c/t^2)⁻¹ → 1`. -/
theorem tendsto_inv_one_sub_div_sq (c : ℝ) :
    Tendsto (fun t : ℝ => (1 - c / t ^ 2)⁻¹) atTop (𝓝 1) := by
  have := tendsto_inv_one_add_div_sq (-c)
  refine this.congr fun t => ?_
  rw [neg_div, ← sub_eq_add_neg]

/-- The Mills ratio for the tail itself, squeezed out of the two-sided bound:
`v\,\varphi(t)/(t\,\Phi(t))\to1`, which is
`-\frac{d}{dt}\P(-V_\infty(0)>t)\sim\frac{t}{\Sigma^2}\P(-V_\infty(0)>t)`
of `sandpile.tex:4993-4995`. -/
theorem tendsto_mills_tail {v : ℝ} (hv : 0 < v) {Phi phi : ℝ → ℝ}
    (hphi : ∀ t : ℝ, 0 < phi t)
    (hupper : ∀ t : ℝ, 0 < t → Phi t ≤ v / t * phi t)
    (hlower : ∀ t : ℝ, 0 < t → (v / t - v ^ 2 / t ^ 3) * phi t ≤ Phi t)
    (hone : Tendsto (fun t : ℝ => (1 - v / t ^ 2)⁻¹) atTop (𝓝 1)) :
    Tendsto (fun t : ℝ => v * phi t / (t * Phi t)) atTop (𝓝 1) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hone ?_ ?_
  · filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_gt_atTop v] with t ht1 htv
    have ht : (0 : ℝ) < t := by linarith
    have hsq : v < t ^ 2 := by nlinarith
    have hp : 0 < phi t := hphi t
    have hl := hlower t ht
    have hcoef : 0 < v / t - v ^ 2 / t ^ 3 := by
      rw [sub_pos, div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_lt_mul_of_pos_left hsq (mul_pos hv ht)]
    have hP : 0 < Phi t := lt_of_lt_of_le (by positivity) hl
    have hu := hupper t ht
    rw [le_div_iff₀ (by positivity)]
    have h1 : t * Phi t ≤ t * (v / t * phi t) := by nlinarith
    have h2 : t * (v / t * phi t) = v * phi t := by field_simp
    nlinarith
  · filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_gt_atTop v] with t ht1 htv
    have ht : (0 : ℝ) < t := by linarith
    have hsq : v < t ^ 2 := by nlinarith
    have hp : 0 < phi t := hphi t
    have hl := hlower t ht
    have hcoef : 0 < v / t - v ^ 2 / t ^ 3 := by
      rw [sub_pos, div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_lt_mul_of_pos_left hsq (mul_pos hv ht)]
    have hP : 0 < Phi t := lt_of_lt_of_le (by positivity) hl
    have hinv : (1 - v / t ^ 2)⁻¹ = t ^ 2 / (t ^ 2 - v) := by
      have h1 : (1 : ℝ) - v / t ^ 2 = (t ^ 2 - v) / t ^ 2 := by field_simp
      rw [h1, inv_div]
    rw [hinv, div_le_div_iff₀ (by positivity) (by nlinarith)]
    have key : v * (t ^ 2 - v) * phi t ≤ t ^ 3 * Phi t := by
      have heq : (v / t - v ^ 2 / t ^ 3) * phi t * t ^ 3 = v * (t ^ 2 - v) * phi t := by
        field_simp
      nlinarith [mul_le_mul_of_nonneg_right hl (by positivity : (0 : ℝ) ≤ t ^ 3)]
    nlinarith

/-- The Mills ratio for the integrated tail, squeezed out of the two two-sided
bounds: `t\,I(t)/(v\,\Phi(t))\to1`, which is
`\E(-V_\infty(0)-t)_+\sim\frac{\Sigma^2}{t}\P(-V_\infty(0)>t)` of
`sandpile.tex:4990-4992`. -/
theorem tendsto_mills_mean {v : ℝ} (hv : 0 < v) {Phi phi I : ℝ → ℝ}
    (hphi : ∀ t : ℝ, 0 < phi t)
    (hupper : ∀ t : ℝ, 0 < t → Phi t ≤ v / t * phi t)
    (hlower : ∀ t : ℝ, 0 < t → (v / t - v ^ 2 / t ^ 3) * phi t ≤ Phi t)
    (hIupper : ∀ t : ℝ, 0 < t → I t ≤ v ^ 2 * phi t / t ^ 2)
    (hIlower : ∀ t : ℝ, 0 < t → v ^ 2 * phi t / (t ^ 2 + 3 * v) ≤ I t)
    (hlow : Tendsto (fun t : ℝ => (1 + 3 * v / t ^ 2)⁻¹) atTop (𝓝 1))
    (hhigh : Tendsto (fun t : ℝ => (1 - v / t ^ 2)⁻¹) atTop (𝓝 1)) :
    Tendsto (fun t : ℝ => t * I t / (v * Phi t)) atTop (𝓝 1) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hhigh ?_ ?_
  · filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_gt_atTop v] with t ht1 htv
    have ht : (0 : ℝ) < t := by linarith
    have hsq : v < t ^ 2 := by nlinarith
    have hp : 0 < phi t := hphi t
    have hl := hlower t ht
    have hcoef : 0 < v / t - v ^ 2 / t ^ 3 := by
      rw [sub_pos, div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_lt_mul_of_pos_left hsq (mul_pos hv ht)]
    have hP : 0 < Phi t := lt_of_lt_of_le (by positivity) hl
    have hIl := hIlower t ht
    have hinv : (1 + 3 * v / t ^ 2)⁻¹ = t ^ 2 / (t ^ 2 + 3 * v) := by
      have h1 : (1 : ℝ) + 3 * v / t ^ 2 = (t ^ 2 + 3 * v) / t ^ 2 := by field_simp
      rw [h1, inv_div]
    rw [hinv, div_le_div_iff₀ (by positivity) (by positivity)]
    have hPu : t ^ 3 * Phi t ≤ v * t ^ 2 * phi t := by
      have hu := hupper t ht
      have heq : t ^ 3 * (v / t * phi t) = v * t ^ 2 * phi t := by field_simp
      nlinarith [mul_le_mul_of_nonneg_left hu (by positivity : (0 : ℝ) ≤ t ^ 3)]
    have hIl2 : v ^ 2 * phi t ≤ (t ^ 2 + 3 * v) * I t := by
      rw [div_le_iff₀ (by positivity)] at hIl
      nlinarith
    nlinarith
  · filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_gt_atTop v] with t ht1 htv
    have ht : (0 : ℝ) < t := by linarith
    have hsq : v < t ^ 2 := by nlinarith
    have hp : 0 < phi t := hphi t
    have hl := hlower t ht
    have hcoef : 0 < v / t - v ^ 2 / t ^ 3 := by
      rw [sub_pos, div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_lt_mul_of_pos_left hsq (mul_pos hv ht)]
    have hP : 0 < Phi t := lt_of_lt_of_le (by positivity) hl
    have hIu := hIupper t ht
    have hinv : (1 - v / t ^ 2)⁻¹ = t ^ 2 / (t ^ 2 - v) := by
      have h1 : (1 : ℝ) - v / t ^ 2 = (t ^ 2 - v) / t ^ 2 := by field_simp
      rw [h1, inv_div]
    rw [hinv, div_le_div_iff₀ (by positivity) (by nlinarith)]
    have hPl : v * (t ^ 2 - v) * phi t ≤ t ^ 3 * Phi t := by
      have heq : (v / t - v ^ 2 / t ^ 3) * phi t * t ^ 3 = v * (t ^ 2 - v) * phi t := by
        field_simp
      nlinarith [mul_le_mul_of_nonneg_right hl (by positivity : (0 : ℝ) ≤ t ^ 3)]
    have hIu2 : t ^ 2 * I t ≤ v ^ 2 * phi t := by
      rw [le_div_iff₀ (by positivity)] at hIu
      nlinarith
    nlinarith

/-- The first-order expansion of the tail of `sandpile.tex:5002-5006`: along a
sequence of levels `t n \to \infty` with increments `dl n` so small that
`t n\,dl n \to 0`, the decrement of the tail is asymptotically `\varphi(t n)\,dl n`. -/
theorem tendsto_tail_expansion {v : ℝ} {Phi phi : ℝ → ℝ} {t dl : ℕ → ℝ}
    (hphi : ∀ s : ℝ, 0 < phi s)
    (htnn : ∀ᶠ n in atTop, 0 ≤ t n)
    (hsub : ∀ s d : ℝ, 0 ≤ s → 0 < d → phi (s + d) * d ≤ Phi s - Phi (s + d))
    (hsub' : ∀ s d : ℝ, 0 ≤ s → 0 < d → Phi s - Phi (s + d) ≤ phi s * d)
    (hratio : ∀ s d : ℝ, phi (s + d) = phi s * Real.exp (-(2 * s * d + d ^ 2) / (2 * v)))
    (hdl : ∀ᶠ n in atTop, 0 < dl n)
    (htd : Tendsto (fun n : ℕ => t n * dl n) atTop (𝓝 0))
    (hd0 : Tendsto dl atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (Phi (t n) - Phi (t n + dl n)) / (phi (t n) * dl n)) atTop (𝓝 1) := by
  have hsqz : Tendsto (fun n : ℕ => dl n ^ 2) atTop (𝓝 0) := by
    simpa using hd0.pow 2
  have hinner : Tendsto (fun n : ℕ => -(2 * t n * dl n + dl n ^ 2) / (2 * v)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => 2 * (t n * dl n)) atTop (𝓝 0) := by
      simpa using htd.const_mul (2 : ℝ)
    have h2 : Tendsto (fun n : ℕ => -(2 * (t n * dl n) + dl n ^ 2)) atTop (𝓝 0) := by
      simpa using (h1.add hsqz).neg
    have h3 := h2.div_const (2 * v)
    simpa [mul_assoc] using h3
  have hexp : Tendsto (fun n : ℕ => Real.exp (-(2 * t n * dl n + dl n ^ 2) / (2 * v)))
      atTop (𝓝 1) := by
    simpa [Function.comp_def] using (Real.continuous_exp.tendsto 0).comp hinner
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hexp tendsto_const_nhds ?_ ?_
  · filter_upwards [hdl, htnn] with n hd hnn
    have hp := hphi (t n)
    rw [le_div_iff₀ (by positivity)]
    have h := hsub (t n) (dl n) hnn hd
    rw [hratio (t n) (dl n)] at h
    nlinarith [h]
  · filter_upwards [hdl, htnn] with n hd hnn
    have hp := hphi (t n)
    rw [div_le_one (by positivity)]
    exact hsub' (t n) (dl n) hnn hd

/-- The mean-increment estimate and the Mills ratio force the product of the level
and its increment to vanish: `\E u_n(0)(\E u_{n+1}(0)-\E u_n(0))\to0` of
`sandpile.tex:5000-5001`. -/
theorem tendsto_level_mul_increment {b I dl t : ℕ → ℝ} {G v : ℝ} (hG : 0 < G) (hv : 0 < v)
    (hbpos : ∀ n, 0 < b n) (hIpos : ∀ᶠ n in atTop, 0 < I n)
    (hbz : Tendsto b atTop (𝓝 0))
    (h1 : Tendsto (fun n : ℕ => G * dl n / I n) atTop (𝓝 1))
    (h2 : Tendsto (fun n : ℕ => t n * I n / (v * b n)) atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => t n * dl n) atTop (𝓝 0) := by
  have h3 : Tendsto (fun n : ℕ => v * b n / G) atTop (𝓝 0) := by
    have h := (hbz.const_mul v).div_const G
    simpa using h
  have key : Tendsto (fun n : ℕ =>
      G * dl n / I n * (t n * I n / (v * b n) * (v * b n / G))) atTop (𝓝 (1 * (1 * 0))) :=
    h1.mul (h2.mul h3)
  rw [show (1 : ℝ) * (1 * 0) = 0 by ring] at key
  refine key.congr' ?_
  filter_upwards [hIpos] with n hn
  have hb : b n ≠ 0 := (hbpos n).ne'
  have hI : I n ≠ 0 := hn.ne'
  have hGne : G ≠ 0 := hG.ne'
  have hvne : v ≠ 0 := hv.ne'
  field_simp

/-- The mean increment is eventually positive. -/
theorem eventually_increment_pos {I dl : ℕ → ℝ} {G : ℝ} (hG : 0 < G)
    (hIpos : ∀ᶠ n in atTop, 0 < I n)
    (h1 : Tendsto (fun n : ℕ => G * dl n / I n) atTop (𝓝 1)) :
    ∀ᶠ n in atTop, 0 < dl n := by
  have h := h1.eventually (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [h, hIpos] with n hn hnI
  by_contra hcon
  rw [not_lt] at hcon
  have hnum : G * dl n ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hG.le hcon
  have hq : G * dl n / I n ≤ 0 := div_nonpos_of_nonpos_of_nonneg hnum hnI.le
  linarith

/-- The mean increment vanishes. -/
theorem tendsto_increment_zero {t dl : ℕ → ℝ}
    (htinf : Tendsto t atTop atTop)
    (hdlpos : ∀ᶠ n in atTop, 0 < dl n)
    (htd : Tendsto (fun n : ℕ => t n * dl n) atTop (𝓝 0)) :
    Tendsto dl atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htd ?_ ?_
  · filter_upwards [hdlpos] with n hn using hn.le
  · filter_upwards [hdlpos, htinf.eventually_ge_atTop (1 : ℝ)] with n hn ht
    nlinarith

end Sandpile
