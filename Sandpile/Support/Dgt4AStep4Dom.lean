import Sandpile.Support.Dgt4AStep4Repr

/-!
# The dominating function of Step 4 of case (a)

The dominating function of Step 4 of case (a) (`sandpile.tex:5267-5295`). The paper
dominates the integrand of `eq:dgt4-gaussian-integral-representation` in two regimes: for
`y\geq0`, `eq:dgt4-gaussian-covariance-sampling` shows that `m_n` is one-Lipschitz in `y`;
since `m_n(0)\to0`, this gives `m_n(y)\leq C(1+y)` and `m_n(y)\rho_n(y)\leq C(1+y)e^{-y}`,
and for `y\leq-1` it uses the concentration bound
`eq:dgt4-gaussian-conditional-concentration`. The Lipschitz half is not needed: terminal
domination already gives `m_n(y)\leq2|y|+1` for all `y` and all large `n`, which is the same
bound with no covariance sampling. Together with the concentration bound of
`Support/Dgt4AStep4Neg.lean` and `\rho_n(y)\leq\rho_n(0)e^{-y}`, the single function
`4(1+|y|)e^{2-|y|}` dominates the whole integrand, and it is integrable on the line.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}

/-- `1+t\leq2e^{t/2}`. -/
theorem one_add_le_two_mul_exp_half (t : ℝ) :
    1 + t ≤ 2 * Real.exp (t / 2) := by
  have h := Real.add_one_le_exp (t / 2)
  linarith

/-- **The dominating function of Step 4 is integrable.** -/
theorem integrable_levelBound : Integrable (fun y : ℝ => (1 + |y|) * Real.exp (2 - |y|)) := by
  set F : ℝ → ℝ := fun t => (1 + t) * Real.exp (2 - t) with hFdef
  have hFm : Measurable F := by
    rw [hFdef]; fun_prop
  have hhalf : IntegrableOn (fun x : ℝ => Real.exp (-(x / 2))) (Ioi 0) := by
    have h := exp_neg_integrableOn_Ioi (0 : ℝ) (b := 1 / 2) (by norm_num)
    refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
    show Real.exp (-(1 / 2 : ℝ) * x) = Real.exp (-(x / 2))
    congr 1
    ring
  have hFIoi : IntegrableOn F (Ioi 0) := by
    refine Integrable.mono' (hhalf.const_mul (2 * Real.exp 2)) hFm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := ht
    have hb := one_add_le_two_mul_exp_half t
    have hFval : F t = (1 + t) * Real.exp (2 - t) := rfl
    rw [Real.norm_eq_abs, hFval, abs_of_nonneg (by positivity)]
    have hsplit : Real.exp (2 - t)
        = Real.exp 2 * (Real.exp (-(t / 2)) * Real.exp (-(t / 2))) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    have hcancel : Real.exp (t / 2) * Real.exp (-(t / 2)) = 1 := by
      rw [← Real.exp_add]
      simp
    calc (1 + t) * Real.exp (2 - t)
        = (1 + t) * (Real.exp 2 * (Real.exp (-(t / 2)) * Real.exp (-(t / 2)))) := by
          rw [hsplit]
      _ ≤ (2 * Real.exp (t / 2))
            * (Real.exp 2 * (Real.exp (-(t / 2)) * Real.exp (-(t / 2)))) := by
          refine mul_le_mul_of_nonneg_right hb (by positivity)
      _ = 2 * Real.exp 2
            * ((Real.exp (t / 2) * Real.exp (-(t / 2))) * Real.exp (-(t / 2))) := by ring
      _ = 2 * Real.exp 2 * Real.exp (-(t / 2)) := by rw [hcancel, one_mul]
  have hIoi : IntegrableOn (fun y : ℝ => F |y|) (Ioi 0) := by
    refine hFIoi.congr_fun (fun x hx => ?_) measurableSet_Ioi
    rw [abs_of_pos hx]
  have hIic : IntegrableOn (fun y : ℝ => F |y|) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    have m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, Set.neg_preimage, Set.neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hIoi
  have : Integrable (fun y : ℝ => F |y|) := by
    rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ))]
    exact hIic.union hIoi
  exact this

/-- `levelDensity` is nonnegative: it is a product of the nonnegative ratio `w/t`, the
Gaussian density `gaussianPDFReal`, and the reciprocal of `gaussianUpperTail`. -/
theorem levelDensity_nonneg (w : ℝ≥0) {t : ℝ} (ht : 0 < t) (y : ℝ) :
    0 ≤ levelDensity w t y := by
  rw [levelDensity]
  have h1 : (0 : ℝ) ≤ gaussianPDFReal 0 w (t + (w : ℝ) * y / t) := gaussianPDFReal_nonneg 0 w _
  have h2 : (0 : ℝ) ≤ gaussianUpperTail w t := ENNReal.toReal_nonneg
  have h3 : (0 : ℝ) ≤ (w : ℝ) / t := div_nonneg w.coe_nonneg ht.le
  positivity

/-- The density-ratio bound `eq:dgt4-gaussian-density-ratio` at finite `t`, before passing to
the limit: `\rho_n(y)\leq\rho_n(0)e^{-y}` in the form `levelDensity w t y
\leq levelDensity w t 0 * e^{-y}`. -/
theorem levelDensity_le (w : ℝ≥0) (hw : w ≠ 0) {t : ℝ} (ht : 0 < t) (y : ℝ) :
    levelDensity w t y ≤ levelDensity w t 0 * Real.exp (-y) := by
  have h := densityRatio_le w hw ht y
  have h0 : levelDensity w t 0 = (w : ℝ) / t * gaussianPDFReal 0 w t / gaussianUpperTail w t := by
    rw [levelDensity, mul_zero, zero_div, add_zero]
  rw [levelDensity, h0]
  exact h

/-- `\rho_n(0)\to1` (`eq:dgt4-gaussian-density-ratio` at `y=0`). -/
theorem tendsto_levelDensity_zero (w : ℝ≥0) (hw : w ≠ 0) {t : ℕ → ℝ}
    (ht : Tendsto t atTop atTop) :
    Tendsto (fun n : ℕ => levelDensity w (t n) 0) atTop (𝓝 1) := by
  have h := (tendsto_density_ratio w hw 0).comp ht
  rw [neg_zero, Real.exp_zero] at h
  exact h

/-- `\rho_n(y)\to e^{-y}` (`eq:dgt4-gaussian-density-ratio`, `sandpile.tex:5245-5251`). -/
theorem tendsto_levelDensity (w : ℝ≥0) (hw : w ≠ 0) {t : ℕ → ℝ}
    (ht : Tendsto t atTop atTop) (y : ℝ) :
    Tendsto (fun n : ℕ => levelDensity w (t n) y) atTop (𝓝 (Real.exp (-y))) :=
  (tendsto_density_ratio w hw y).comp ht

/-- `condMeanReflected` is nonnegative, being the integral of the pointwise maximum of the
reflected increment with `0`. -/
theorem condMeanReflected_nonneg (hd : 5 ≤ d) (v : ℝ≥0) (n : ℕ) (y : ℝ) :
    0 ≤ condMeanReflected d hd v n y :=
  integral_nonneg fun _ => le_max_right _ _

/-- **The terminal bound on the conditional mean** (`sandpile.tex:5268-5272`): for all large
`n` and every level, `m_n(y)\leq2|y|+1`.  This replaces the paper's Lipschitz argument. -/
theorem eventually_condMeanReflected_le (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    (v : ℝ≥0) (hv : v ≠ 0) (hsq : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 v)) :
    ∀ᶠ n : ℕ in atTop, ∀ y : ℝ, condMeanReflected d hd v n y ≤ 2 * |y| + 1 := by
  set ρ : Measure (Site d → ℝ) :=
    (LatticeProb.gaussLaw (Site d)).map (residField d hd) with hρ
  haveI : IsProbabilityMeasure ρ := by
    rw [hρ]
    exact Measure.isProbabilityMeasure_map (measurable_residField hd).aemeasurable
  set S : ℝ := ((fieldVar d v : ℝ≥0) : ℝ) with hSdef
  have hSpos : (0 : ℝ) < S := coe_pos_of_ne_zero (fieldVar_ne_zero hd hv)
  set cc : ℝ := Real.sqrt (v : ℝ) with hccdef
  set a : ℕ → ℝ := fun n => meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n with hadef
  set p : ℕ → ℝ := fun n => ((dgt4Horizon d n + 1 : ℕ) : ℝ) ^ ((4 - (d : ℝ)) / 4) with hpdef
  have hk1 : ∀ n : ℕ, 1 ≤ dgt4Horizon d n + 1 := fun _ => Nat.succ_le_succ (Nat.zero_le _)
  have haval : ∀ m : ℕ, meanOdometer (centeredMassLaw d (gaussianReal 0 v)) m = a m :=
    fun _ => rfl
  obtain ⟨C₂, hC₂, eps, heps, hterm⟩ := exists_integral_condTerminal_condLevel_le hGH hd v hv hsq
  have hatt := tendsto_meanOdometer_gaussian_atTop hGH hd v hv
  have hCp : Tendsto (fun n : ℕ => C₂ * p n) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_horizon_rpow (d := d) hd).const_mul C₂
  filter_upwards [hatt.eventually_gt_atTop 0, eventually_dgt4Horizon_le hd,
    heps.eventually_le_const (by norm_num : (0 : ℝ) < 1),
    hCp.eventually_le_const (by norm_num : (0 : ℝ) < 1)] with n ha hkle hepsn hCpn
  intro y
  set s : ℝ := condLevel d hd v y n with hsdef
  set T : (Site d → ℝ) → ℝ :=
    condTerminal d hd cc s (a n) (n - dgt4Horizon d n) (dgt4Horizon d n + 1) with hTdef
  have hTint : Integrable T ρ :=
    integrable_condTerminal hGH hd v hsq (a n) (n - dgt4Horizon d n) (dgt4Horizon d n + 1)
      (hk1 n) s
  have hbound : Integrable (fun r => |y| + a n / S * T r) ρ :=
    (integrable_const |y|).add (hTint.const_mul _)
  have hdom : (condMeanReflected d hd v n y) ≤ ∫ r, (|y| + a n / S * T r) ∂ρ := by
    rw [condMeanReflected, ← hSdef, ← hccdef, ← hρ, ← hsdef, haval n]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun r => le_max_right _ _)
      hbound ?_
    filter_upwards [ae_mem_condConv hd cc s, ae_infiniteGreenField_condLevel hd hv y n]
      with r hr hlev
    have h := condReflected_pos_le hd cc s (a n) S y hSpos ha (dgt4Horizon d n) n hkle r hr hlev
    rwa [mul_max_of_nonneg _ _ (div_nonneg ha.le hSpos.le), mul_zero] at h
  have hsplit : (∫ r, (|y| + a n / S * T r) ∂ρ) = |y| + a n / S * ∫ r, T r ∂ρ := by
    rw [integral_add (integrable_const |y|) (hTint.const_mul _), integral_const,
      integral_const_mul]
    simp
  have hterm' := hterm n ha y
  have hle : a n / S * (∫ r, T r ∂ρ) ≤ eps n + C₂ * p n * |y| := hterm'
  have habs : (0 : ℝ) ≤ |y| := abs_nonneg y
  have hCy : C₂ * p n * |y| ≤ |y| := by nlinarith [hCpn, habs]
  rw [hsplit] at hdom
  linarith

/-- **The dominating function of Step 4** (`sandpile.tex:5286-5290`): for all large `n` the
integrand of `eq:dgt4-gaussian-integral-representation` is at most
`4(1+|y|)e^{2-|y|}` at every level. -/
theorem eventually_condMeanReflected_mul_levelDensity_le
    (hGaussConc : Sandpile.External.GaussianLipschitzConcentration)
    (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    (v : ℝ≥0) (hv : v ≠ 0) (hsq : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 v)) :
    ∀ᶠ n : ℕ in atTop, ∀ y : ℝ,
      condMeanReflected d hd v n y
          * levelDensity (fieldVar d v) (meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n) y
        ≤ 4 * ((1 + |y|) * Real.exp (2 - |y|)) := by
  set a : ℕ → ℝ := fun n => meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n with hadef
  have hatt := tendsto_meanOdometer_gaussian_atTop hGH hd v hv
  have hw : fieldVar d v ≠ 0 := fieldVar_ne_zero hd hv
  have hdens0 : Tendsto (fun n : ℕ => levelDensity (fieldVar d v) (a n) 0) atTop (𝓝 1) :=
    tendsto_levelDensity_zero (fieldVar d v) hw hatt
  filter_upwards [hatt.eventually_gt_atTop 0,
    eventually_condMeanReflected_le hGH hd v hv hsq,
    eventually_integral_condReflected_posPart_le hGaussConc hGH hd v hv hsq,
    hdens0.eventually_le_const (by norm_num : (1 : ℝ) < 2)] with n ha hm hneg hd0
  intro y
  have hmnn : 0 ≤ condMeanReflected d hd v n y := condMeanReflected_nonneg hd v n y
  have hdnn : 0 ≤ levelDensity (fieldVar d v) (a n) y := levelDensity_nonneg _ ha y
  have hdle : levelDensity (fieldVar d v) (a n) y
      ≤ 2 * Real.exp (-y) := by
    have h := levelDensity_le (fieldVar d v) hw ha y
    have hexp : (0 : ℝ) < Real.exp (-y) := Real.exp_pos _
    nlinarith [h, hd0, hexp]
  have habs : (0 : ℝ) ≤ |y| := abs_nonneg y
  have hyle : -y ≤ |y| := neg_le_abs y
  rcases le_or_gt (-1 : ℝ) y with hy | hy
  · -- `y \geq -1`
    have hexpy : Real.exp (-y) ≤ Real.exp (2 - |y|) := by
      refine Real.exp_le_exp.2 ?_
      rcases le_or_gt 0 y with h | h
      · rw [abs_of_nonneg h]; linarith
      · rw [abs_of_neg h]; linarith
    have hmle : condMeanReflected d hd v n y ≤ 2 * (1 + |y|) := by
      have := hm y
      linarith
    calc condMeanReflected d hd v n y * levelDensity (fieldVar d v) (a n) y
        ≤ (2 * (1 + |y|)) * (2 * Real.exp (-y)) := by
          refine mul_le_mul hmle hdle hdnn (by linarith)
      _ ≤ (2 * (1 + |y|)) * (2 * Real.exp (2 - |y|)) := by
          refine mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      _ = 4 * ((1 + |y|) * Real.exp (2 - |y|)) := by ring
  · -- `y \leq -1`
    have hy1 : y ≤ -1 := by linarith
    have hyneg : y < 0 := by linarith
    have habsy : |y| = -y := abs_of_neg hyneg
    have hmle : condMeanReflected d hd v n y ≤ Real.exp (-(2 * |y|)) := hneg y hy1
    have hprod : Real.exp (-(2 * |y|)) * (2 * Real.exp (-y))
        ≤ 4 * ((1 + |y|) * Real.exp (2 - |y|)) := by
      have hcomb : Real.exp (-(2 * |y|)) * Real.exp (-y) = Real.exp (-|y|) := by
        rw [← Real.exp_add]
        congr 1
        rw [habsy]
        ring
      have hmono : Real.exp (-|y|) ≤ Real.exp (2 - |y|) :=
        Real.exp_le_exp.2 (by linarith)
      have hpos : (0 : ℝ) < Real.exp (2 - |y|) := Real.exp_pos _
      nlinarith [hcomb, hmono, habs, hpos]
    calc condMeanReflected d hd v n y * levelDensity (fieldVar d v) (a n) y
        ≤ Real.exp (-(2 * |y|)) * (2 * Real.exp (-y)) := by
          refine mul_le_mul hmle hdle hdnn (Real.exp_nonneg _)
      _ ≤ 4 * ((1 + |y|) * Real.exp (2 - |y|)) := hprod

end Sandpile
