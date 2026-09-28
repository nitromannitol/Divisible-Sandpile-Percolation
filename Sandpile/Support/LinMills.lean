import LatticeProb.Gauss.TailMills

/-! # Sharp Mills Asymptotics

The sharp Mills asymptotics that case (a) of `prop:dgt4-contact-asymptotics` opens with
(`sandpile.tex:4969` ff.).  The paper uses two displays about the Gaussian threshold field
`J = -V_∞`, of variance `Σ² = Var(ζ(0))∑_z G(0,z)²`:

  `E(-V_∞(0)-t)_+ ∼ (Σ²/t) P(-V_∞(0)>t)` and
  `-\frac{d}{dt} P(-V_∞(0)>t) ∼ (t/Σ²) P(-V_∞(0)>t)` .

`Support/LinGaussTail.lean` proves the first in quantitative form
(`abs_meanOvershoot_sub_le`) together with the three Mills bounds it rests on.  This file
puts the second in the form the proposition uses: the sandwich

  `(1 - v/t²) φ_v(t) ≤ (t/v) P(Z>t) ≤ (1 - v/t² + 3v²/t⁴) φ_v(t)`,

which is the sharp second-order lower bound and third-order upper bound of `LinGaussTail`
multiplied by `t/v`, and the limit it forces,

  `(t/v) P(Z>t) / φ_v(t) → 1`  as `t → ∞`,

which IS the paper's `φ_v(t) ∼ (t/v) P(Z>t)`, since `-d/dt P(Z>t) = φ_v(t)`.
-/

open LatticeProb.GaussTail

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile

/-- **The sharp Mills sandwich, rescaled.**  `(t/v) P(Z>t)` sits between `(1 - v/t²) φ_v(t)`
and `(1 - v/t² + 3v²/t⁴) φ_v(t)`. -/
theorem tail_density_sandwich {v : ℝ≥0} (hv : 0 < (v : ℝ)) {t : ℝ} (ht : 0 < t) :
    (1 - (v : ℝ) / t ^ 2) * gaussianPDFReal 0 v t
        ≤ t / (v : ℝ) * ((gaussianReal 0 v).real (Set.Ioi t)) ∧
      t / (v : ℝ) * ((gaussianReal 0 v).real (Set.Ioi t))
        ≤ (1 - (v : ℝ) / t ^ 2 + 3 * (v : ℝ) ^ 2 / t ^ 4) * gaussianPDFReal 0 v t := by
  have hlow := gaussianReal_real_Ioi_ge_sharp hv ht
  have hup := gaussianReal_real_Ioi_le_sharp hv ht
  have hpos : (0:ℝ) < t / (v : ℝ) := div_pos ht hv
  have hid1 : t / (v : ℝ) * (((v : ℝ) / t - (v : ℝ) ^ 2 / t ^ 3) * gaussianPDFReal 0 v t)
      = (1 - (v : ℝ) / t ^ 2) * gaussianPDFReal 0 v t := by
    field_simp
  have hid2 : t / (v : ℝ) *
      (((v : ℝ) / t - (v : ℝ) ^ 2 / t ^ 3 + 3 * (v : ℝ) ^ 3 / t ^ 5) *
        gaussianPDFReal 0 v t)
      = (1 - (v : ℝ) / t ^ 2 + 3 * (v : ℝ) ^ 2 / t ^ 4) * gaussianPDFReal 0 v t := by
    field_simp
  refine ⟨?_, ?_⟩
  · have h := mul_le_mul_of_nonneg_left hlow hpos.le
    rw [hid1] at h
    exact h
  · have h := mul_le_mul_of_nonneg_left hup hpos.le
    rw [hid2] at h
    exact h

/-- The ratio of the rescaled tail to the density is squeezed between two quantities that
tend to one. -/
theorem tail_density_ratio_bounds {v : ℝ≥0} (hv : 0 < (v : ℝ)) {t : ℝ} (ht : 0 < t) :
    1 - (v : ℝ) / t ^ 2
        ≤ t / (v : ℝ) * ((gaussianReal 0 v).real (Set.Ioi t)) / gaussianPDFReal 0 v t ∧
      t / (v : ℝ) * ((gaussianReal 0 v).real (Set.Ioi t)) / gaussianPDFReal 0 v t
        ≤ 1 - (v : ℝ) / t ^ 2 + 3 * (v : ℝ) ^ 2 / t ^ 4 := by
  have hvne : v ≠ 0 := fun h => by rw [h] at hv; simp at hv
  have hphi : 0 < gaussianPDFReal 0 v t := gaussianPDFReal_pos 0 v t hvne
  obtain ⟨h1, h2⟩ := tail_density_sandwich hv ht
  refine ⟨?_, ?_⟩
  · rw [le_div_iff₀ hphi]
    exact h1
  · rw [div_le_iff₀ hphi]
    exact h2

/-- **The second display of case (a) of `prop:dgt4-contact-asymptotics`.**  Since
`-d/dt P(Z>t) = φ_v(t)`, this is `-d/dt P(Z>t) ∼ (t/Σ²) P(Z>t)`. -/
theorem tendsto_tail_density_ratio {v : ℝ≥0} (hv : 0 < (v : ℝ)) :
    Tendsto (fun t : ℝ =>
        t / (v : ℝ) * ((gaussianReal 0 v).real (Set.Ioi t)) / gaussianPDFReal 0 v t)
      atTop (𝓝 1) := by
  have hsq : Tendsto (fun t : ℝ => t ^ 2) atTop atTop := tendsto_pow_atTop (by norm_num)
  have hq4 : Tendsto (fun t : ℝ => t ^ 4) atTop atTop := tendsto_pow_atTop (by norm_num)
  have h2 : Tendsto (fun t : ℝ => (v : ℝ) / t ^ 2) atTop (𝓝 0) :=
    hsq.const_div_atTop _
  have h4 : Tendsto (fun t : ℝ => 3 * (v : ℝ) ^ 2 / t ^ 4) atTop (𝓝 0) :=
    hq4.const_div_atTop _
  have hlow : Tendsto (fun t : ℝ => 1 - (v : ℝ) / t ^ 2) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub h2
  have hup : Tendsto
      (fun t : ℝ => 1 - (v : ℝ) / t ^ 2 + 3 * (v : ℝ) ^ 2 / t ^ 4) atTop (𝓝 1) := by
    simpa using hlow.add h4
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    exact (tail_density_ratio_bounds hv ht).1
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    exact (tail_density_ratio_bounds hv ht).2

/-! ### The mean overshoot against the tail, in ratio form -/

/-- The relative error of the mean overshoot against `(v/t) P(Z>t)`. -/
theorem abs_meanOvershoot_ratio_sub_one_le {v : ℝ≥0} (hv : 0 < (v : ℝ)) {t : ℝ}
    (ht : 0 < t) (ht2 : (v : ℝ) < t ^ 2) :
    |(∫ x in Set.Ioi t, (x - t) * gaussianPDFReal 0 v x)
          / ((v : ℝ) / t * ((gaussianReal 0 v).real (Set.Ioi t))) - 1|
      ≤ (2 * (v : ℝ) / t ^ 2 + 3 * (v : ℝ) ^ 2 / t ^ 4) / (1 - (v : ℝ) / t ^ 2) := by
  have hvne : v ≠ 0 := fun h => by rw [h] at hv; simp at hv
  have hphi : 0 < gaussianPDFReal 0 v t := gaussianPDFReal_pos 0 v t hvne
  have ht2' : (0:ℝ) < t ^ 2 := by positivity
  have ht4' : (0:ℝ) < t ^ 4 := by positivity
  have hone : (0:ℝ) < 1 - (v : ℝ) / t ^ 2 := by
    rw [sub_pos, div_lt_one ht2']
    exact ht2
  have hfac : 0 < (v : ℝ) ^ 2 / t ^ 2 - (v : ℝ) ^ 3 / t ^ 4 := by
    have hid : (v : ℝ) ^ 2 / t ^ 2 - (v : ℝ) ^ 3 / t ^ 4
        = ((v : ℝ) ^ 2 / t ^ 2) * (1 - (v : ℝ) / t ^ 2) := by
      field_simp
    rw [hid]
    positivity
  have hvt : (0:ℝ) < (v : ℝ) / t := div_pos hv ht
  have hD : ((v : ℝ) ^ 2 / t ^ 2 - (v : ℝ) ^ 3 / t ^ 4) * gaussianPDFReal 0 v t
      ≤ (v : ℝ) / t * ((gaussianReal 0 v).real (Set.Ioi t)) := by
    have h := mul_le_mul_of_nonneg_left (gaussianReal_real_Ioi_ge_sharp hv ht) hvt.le
    have hid : (v : ℝ) / t * (((v : ℝ) / t - (v : ℝ) ^ 2 / t ^ 3) * gaussianPDFReal 0 v t)
        = ((v : ℝ) ^ 2 / t ^ 2 - (v : ℝ) ^ 3 / t ^ 4) * gaussianPDFReal 0 v t := by
      field_simp
    rw [hid] at h
    exact h
  have hDpos : 0 < (v : ℝ) / t * ((gaussianReal 0 v).real (Set.Ioi t)) :=
    lt_of_lt_of_le (mul_pos hfac hphi) hD
  have hnum := LatticeProb.GaussTail.abs_meanOvershoot_sub_le hv ht
  have hrhs : (0:ℝ)
      ≤ (2 * (v : ℝ) / t ^ 2 + 3 * (v : ℝ) ^ 2 / t ^ 4) / (1 - (v : ℝ) / t ^ 2) := by
    positivity
  have hsub : (∫ x in Set.Ioi t, (x - t) * gaussianPDFReal 0 v x)
        / ((v : ℝ) / t * ((gaussianReal 0 v).real (Set.Ioi t))) - 1
      = ((∫ x in Set.Ioi t, (x - t) * gaussianPDFReal 0 v x)
          - (v : ℝ) / t * ((gaussianReal 0 v).real (Set.Ioi t)))
        / ((v : ℝ) / t * ((gaussianReal 0 v).real (Set.Ioi t))) :=
    div_sub_one hDpos.ne'
  rw [hsub, abs_div, abs_of_pos hDpos, div_le_iff₀ hDpos]
  have hcoef : (2 * (v : ℝ) / t ^ 2 + 3 * (v : ℝ) ^ 2 / t ^ 4) / (1 - (v : ℝ) / t ^ 2)
      * (((v : ℝ) ^ 2 / t ^ 2 - (v : ℝ) ^ 3 / t ^ 4) * gaussianPDFReal 0 v t)
      = (2 * (v : ℝ) ^ 3 / t ^ 4 + 3 * (v : ℝ) ^ 4 / t ^ 6) * gaussianPDFReal 0 v t := by
    have hne : t ^ 2 - (v : ℝ) ≠ 0 := by nlinarith
    field_simp
  have hkey : (2 * (v : ℝ) ^ 3 / t ^ 4 + 3 * (v : ℝ) ^ 4 / t ^ 6) * gaussianPDFReal 0 v t
      ≤ (2 * (v : ℝ) / t ^ 2 + 3 * (v : ℝ) ^ 2 / t ^ 4) / (1 - (v : ℝ) / t ^ 2)
        * ((v : ℝ) / t * ((gaussianReal 0 v).real (Set.Ioi t))) := by
    calc (2 * (v : ℝ) ^ 3 / t ^ 4 + 3 * (v : ℝ) ^ 4 / t ^ 6) * gaussianPDFReal 0 v t
        = (2 * (v : ℝ) / t ^ 2 + 3 * (v : ℝ) ^ 2 / t ^ 4) / (1 - (v : ℝ) / t ^ 2)
          * (((v : ℝ) ^ 2 / t ^ 2 - (v : ℝ) ^ 3 / t ^ 4) * gaussianPDFReal 0 v t) := hcoef.symm
      _ ≤ (2 * (v : ℝ) / t ^ 2 + 3 * (v : ℝ) ^ 2 / t ^ 4) / (1 - (v : ℝ) / t ^ 2)
          * ((v : ℝ) / t * ((gaussianReal 0 v).real (Set.Ioi t))) :=
          mul_le_mul_of_nonneg_left hD hrhs
  linarith [hnum, hkey]

/-- **The first display of case (a) of `prop:dgt4-contact-asymptotics`,**
`E(Z-t)_+ ∼ (Σ²/t) P(Z>t)`. -/
theorem tendsto_meanOvershoot_ratio {v : ℝ≥0} (hv : 0 < (v : ℝ)) :
    Tendsto (fun t : ℝ => (∫ x in Set.Ioi t, (x - t) * gaussianPDFReal 0 v x)
        / ((v : ℝ) / t * ((gaussianReal 0 v).real (Set.Ioi t)))) atTop (𝓝 1) := by
  have hsq : Tendsto (fun t : ℝ => t ^ 2) atTop atTop := tendsto_pow_atTop (by norm_num)
  have hq4 : Tendsto (fun t : ℝ => t ^ 4) atTop atTop := tendsto_pow_atTop (by norm_num)
  have h2 : Tendsto (fun t : ℝ => 2 * (v : ℝ) / t ^ 2) atTop (𝓝 0) := hsq.const_div_atTop _
  have h4 : Tendsto (fun t : ℝ => 3 * (v : ℝ) ^ 2 / t ^ 4) atTop (𝓝 0) := hq4.const_div_atTop _
  have hv2 : Tendsto (fun t : ℝ => (v : ℝ) / t ^ 2) atTop (𝓝 0) := hsq.const_div_atTop _
  have hden : Tendsto (fun t : ℝ => 1 - (v : ℝ) / t ^ 2) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hv2
  have hbound : Tendsto
      (fun t : ℝ => (2 * (v : ℝ) / t ^ 2 + 3 * (v : ℝ) ^ 2 / t ^ 4) / (1 - (v : ℝ) / t ^ 2))
      atTop (𝓝 0) := by
    have hinv : Tendsto (fun t : ℝ => (1 - (v : ℝ) / t ^ 2)⁻¹) atTop (𝓝 1) := by
      simpa using hden.inv₀ one_ne_zero
    have h := (h2.add h4).mul hinv
    simpa [div_eq_mul_inv] using h
  rw [← sub_zero (1 : ℝ)]
  have hz : Tendsto (fun t : ℝ => (∫ x in Set.Ioi t, (x - t) * gaussianPDFReal 0 v x)
      / ((v : ℝ) / t * ((gaussianReal 0 v).real (Set.Ioi t))) - 1) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [eventually_gt_atTop (0:ℝ), eventually_gt_atTop (Real.sqrt (v : ℝ))]
      with t ht htv
    have ht2 : (v : ℝ) < t ^ 2 := by
      have := Real.sq_sqrt hv.le
      nlinarith [Real.sqrt_nonneg (v : ℝ), htv]
    simpa [Real.norm_eq_abs] using abs_meanOvershoot_ratio_sub_one_le hv ht ht2
  simpa using hz.add (tendsto_const_nhds (x := (1:ℝ)))

/-! ### From increments to linear growth -/

/-- If the increments of a real sequence converge, the sequence grows linearly at that
rate.  This is the Cesàro step of case (a) of `prop:dgt4-contact-asymptotics`: from
`1/P(>E u_{n+1}) - 1/P(>E u_n) → 1/G(0,0)` it gives `P(>E u_n)^{-1} ∼ n/G(0,0)`. -/
theorem tendsto_div_natCast_of_sub_tendsto {a : ℕ → ℝ} {L : ℝ}
    (h : Tendsto (fun n : ℕ => a (n + 1) - a n) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => a n / (n : ℝ)) atTop (𝓝 L) := by
  have h1 : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * (a n - a 0)) atTop (𝓝 L) := by
    refine h.cesaro.congr ?_
    intro n
    rw [Finset.sum_range_sub a n]
  have h2 : Tendsto (fun n : ℕ => a 0 / (n : ℝ)) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_natCast_atTop_atTop
  have h3 : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * (a n - a 0) + a 0 / (n : ℝ)) atTop (𝓝 L) := by
    simpa using h1.add h2
  refine h3.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  have hn0 : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp
  ring

/-! ### The derivative of the tail -/

/-- **`-d/dt P(Z>t) = φ_v(t)`.**  The Gaussian upper tail is differentiable in the level,
with derivative minus the density.  With `tendsto_tail_density_ratio` this is the paper's
`-\frac{d}{dt}\P(-V_\infty(0)>t)\sim\frac{t}{\Sigma^2}\P(-V_\infty(0)>t)`. -/
theorem hasDerivAt_gaussianReal_real_Ioi {v : ℝ≥0} (hv : 0 < (v : ℝ)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (gaussianReal 0 v).real (Set.Ioi s))
      (-gaussianPDFReal 0 v t) t := by
  have hvne : v ≠ 0 := fun h => by rw [h] at hv; simp at hv
  have hint : Integrable (gaussianPDFReal 0 v) := integrable_gaussianPDFReal 0 v
  have hcont : Continuous (gaussianPDFReal 0 v) :=
    continuous_iff_continuousAt.mpr fun x => (hasDerivAt_gaussianPDFReal hv x).continuousAt
  have hIic : ∀ s : ℝ, IntegrableOn (gaussianPDFReal 0 v) (Set.Iic s) :=
    fun s => hint.integrableOn
  have hcompl : ∀ s : ℝ, (gaussianReal 0 v).real (Set.Ioi s)
      = 1 - ∫ x in Set.Iic s, gaussianPDFReal 0 v x := by
    intro s
    have hadd := MeasureTheory.integral_add_compl (measurableSet_Iic (a := s)) hint
    rw [integral_gaussianPDFReal_eq_one 0 hvne] at hadd
    rw [gaussianReal_real_Ioi_eq_integral hvne s, Set.compl_Iic] at *
    linarith
  have heq : ∀ s : ℝ, (gaussianReal 0 v).real (Set.Ioi s)
      = (1 - ∫ x in Set.Iic t, gaussianPDFReal 0 v x)
        - ∫ x in t..s, gaussianPDFReal 0 v x := by
    intro s
    rw [hcompl s, ← intervalIntegral.integral_Iic_sub_Iic (hIic t) (hIic s)]
    ring
  have hd : HasDerivAt (fun s : ℝ => ∫ x in t..s, gaussianPDFReal 0 v x)
      (gaussianPDFReal 0 v t) t :=
    intervalIntegral.integral_hasDerivAt_right hint.intervalIntegrable
      (hcont.stronglyMeasurable.stronglyMeasurableAtFilter) hcont.continuousAt
  refine (hd.const_sub (1 - ∫ x in Set.Iic t, gaussianPDFReal 0 v x)).congr_of_eventuallyEq ?_
  filter_upwards with s
  exact heq s

/-! ### The level of Step 1 of `lem:dgt4-path-survival` -/

/-- **The level forced by the tail.**  If the Gaussian upper tail at `a ≥ √v` is at most `p`
and the standardized level `a/√v` is at most `M`, then `a²/v ≥ -2 log p - 2 log M - 6`.
With `p = C R^{-2}` from `eq:dgt4-uniform-contact-thresholds` and `M = C√(log R)` from the
Chernoff bound (`LatticeProb.Isonormal.gaussianReal_measure_ge_le`), this is the paper's
`b_x²/\Var(J(0)) = 4 \log R - \log\log R + O_{ε,T}(1)` as a LOWER bound, which is the form
`Sandpile.pair_term_le` consumes. -/
theorem level_lower_bound {v : ℝ≥0} (hv : 0 < (v : ℝ)) {a p M : ℝ}
    (ha : Real.sqrt (v : ℝ) ≤ a) (hp : ((gaussianReal 0 v).real (Set.Ioi a)) ≤ p)
    (hub : a / Real.sqrt (v : ℝ) ≤ M) :
    -2 * Real.log p - 2 * Real.log M - 6 ≤ a ^ 2 / (v : ℝ) := by
  have hs : 0 < Real.sqrt (v : ℝ) := Real.sqrt_pos.mpr hv
  have ha0 : 0 < a := lt_of_lt_of_le hs ha
  have hinv := log_le_of_gaussianReal_tail_le hv ha hp
  have hlog : Real.log (a / Real.sqrt (v : ℝ)) ≤ Real.log M :=
    Real.log_le_log (by positivity) hub
  have hhalf : a ^ 2 / (2 * (v : ℝ)) = a ^ 2 / (v : ℝ) / 2 := by
    field_simp
  rw [hhalf] at hinv
  linarith

end Sandpile
