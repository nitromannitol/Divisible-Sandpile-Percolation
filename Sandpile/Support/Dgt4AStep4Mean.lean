/-
**Step 4 of case (a) for the mean increment** (`sandpile.tex:5291-5301`): dominated
convergence in the integral representation, and the passage from

  `\int_\R m_n(y)\rho_n(y)\,dy\longrightarrow\int_0^\infty\frac{y}{G(0,0)}e^{-y}\,dy
     =\frac1{G(0,0)}`

to `eq:dgt4-contact-mean-increment`, `G(0,0)(\E u_{n+1}(0)-\E u_n(0))/
\E(-V_\infty(0)-\E u_n(0))_+\to1`.  The last step is the Mills ratio: the integrated tail
`\E(N(0,\Sigma^2)-t)_+` is asymptotic to `\Sigma^2\P(N(0,\Sigma^2)>t)/t`.
-/
import Sandpile.Support.Dgt4AStep4Dom

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}

theorem measurable_condLevel (hd : 5 ≤ d) (v : ℝ≥0) (n : ℕ) :
    Measurable (fun y : ℝ => condLevel d hd v y n) := by
  unfold condLevel
  fun_prop

theorem measurable_condReflected_pair (hd : 5 ≤ d) (c : ℝ) (v : ℝ≥0) (n t : ℕ) :
    Measurable (fun p : ℝ × (Site d → ℝ) =>
      condReflected d hd c (condLevel d hd v p.1 n) t p.2) := by
  have hcs : Measurable (fun p : ℝ × (Site d → ℝ) =>
      condScenery d hd c p.2 (condLevel d hd v p.1 n)) := by
    refine measurable_pi_lambda _ fun z => ?_
    show Measurable fun p : ℝ × (Site d → ℝ) =>
      c * (p.2 z + condLevel d hd v p.1 n * (greenUnit d hd : Site d → ℝ) z)
    refine Measurable.const_mul ?_ c
    refine Measurable.add ((measurable_pi_apply z).comp measurable_snd) ?_
    exact ((measurable_condLevel hd v n).comp measurable_fst).mul_const _
  have h1 : Measurable (fun p : ℝ × (Site d → ℝ) =>
      -(condScenery d hd c p.2 (condLevel d hd v p.1 n)) 0) :=
    (((measurable_pi_apply (0 : Site d)).comp hcs)).neg
  have h2 : Measurable (fun p : ℝ × (Site d → ℝ) =>
      avg (odometerOf (condScenery d hd c p.2 (condLevel d hd v p.1 n)) t) 0) := by
    unfold avg LatticeProb.walkOp
    exact (Finset.measurable_sum _ fun i _ =>
      (((measurable_odometerOf t _).comp hcs)).add
        (((measurable_odometerOf t _).comp hcs))).div_const _
  exact h1.sub h2

theorem measurable_condMeanReflected (hd : 5 ≤ d) (v : ℝ≥0) (n : ℕ) :
    Measurable (fun y : ℝ => condMeanReflected d hd v n y) := by
  haveI : IsProbabilityMeasure ((LatticeProb.gaussLaw (Site d)).map (residField d hd)) :=
    Measure.isProbabilityMeasure_map (measurable_residField hd).aemeasurable
  have hjoint : StronglyMeasurable (fun p : ℝ × (Site d → ℝ) =>
      max (meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n
        / ((fieldVar d v : ℝ≥0) : ℝ)
        * condReflected d hd (Real.sqrt (v : ℝ)) (condLevel d hd v p.1 n) n p.2) 0) :=
    (((measurable_condReflected_pair hd (Real.sqrt (v : ℝ)) v n n).const_mul _).max
      measurable_const).stronglyMeasurable
  exact hjoint.integral_prod_right'.measurable

theorem measurable_levelDensity (w : ℝ≥0) (t : ℝ) :
    Measurable (fun y : ℝ => levelDensity w t y) := by
  unfold levelDensity gaussianPDFReal
  fun_prop

/-- `\int_\R\max(y,0)e^{-y}\,dy=1` (`sandpile.tex:5294-5296`). -/
theorem integral_maxPart_mul_exp_neg : (∫ y : ℝ, max y 0 * Real.exp (-y)) = 1 := by
  have hcont : Continuous (fun y : ℝ => max y 0 * Real.exp (-y)) := by fun_prop
  have hint : Integrable (fun y : ℝ => max y 0 * Real.exp (-y)) := by
    refine Integrable.mono' integrable_levelBound hcont.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun y => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rcases le_or_gt y 0 with h | h
    · rw [max_eq_right h, zero_mul]
      positivity
    · rw [max_eq_left h.le, abs_of_pos h]
      have hexp : Real.exp (-y) ≤ Real.exp (2 - y) := Real.exp_le_exp.2 (by linarith)
      have h2 : (0 : ℝ) < Real.exp (-y) := Real.exp_pos _
      have h3 : (0 : ℝ) < Real.exp (2 - y) := Real.exp_pos _
      nlinarith [hexp, h2, h3, h]
  have hsplit := integral_add_compl (measurableSet_Ioi (a := (0 : ℝ))) hint
  have hzero : (∫ y in (Ioi (0 : ℝ))ᶜ, max y 0 * Real.exp (-y)) = 0 := by
    rw [compl_Ioi]
    refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
    have hy0 : y ≤ 0 := hy
    rw [max_eq_right hy0, zero_mul]
  have hIoi : (∫ y in Ioi (0 : ℝ), max y 0 * Real.exp (-y)) = 1 := by
    rw [← integral_Ioi_id_mul_exp_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    have hy0 : (0 : ℝ) < y := hy
    rw [max_eq_left hy0.le]
  rw [hzero, hIoi, add_zero] at hsplit
  exact hsplit.symm

/-- The limit of the integral representation (`sandpile.tex:5294-5296`). -/
theorem integral_limit_value {G : ℝ} (hG : 0 < G) :
    (∫ y : ℝ, max y 0 / G * Real.exp (-y)) = 1 / G := by
  have hrw : (∫ y : ℝ, max y 0 / G * Real.exp (-y))
      = G⁻¹ * ∫ y : ℝ, max y 0 * Real.exp (-y) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    field_simp
  rw [hrw, integral_maxPart_mul_exp_neg, mul_one, inv_eq_one_div]

/-- **Dominated convergence in the integral representation** (`sandpile.tex:5286-5296`). -/
theorem tendsto_integral_condMeanReflected_levelDensity
    (hGaussConc : Sandpile.External.GaussianLipschitzConcentration)
    (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    (v : ℝ≥0) (hv : v ≠ 0) (hsq : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 v)) :
    Tendsto (fun n : ℕ => ∫ y : ℝ, condMeanReflected d hd v n y
        * levelDensity (fieldVar d v)
            (meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n) y)
      atTop (𝓝 (1 / green d 0 0)) := by
  have hGpos : (0 : ℝ) < green d 0 0 :=
    lt_of_lt_of_le zero_lt_one (Sandpile.one_le_green (by omega))
  have hw : fieldVar d v ≠ 0 := fieldVar_ne_zero hd hv
  have hatt := tendsto_meanOdometer_gaussian_atTop hGH hd v hv
  rw [← integral_limit_value hGpos]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun y : ℝ => 4 * ((1 + |y|) * Real.exp (2 - |y|))) ?_ ?_
    (integrable_levelBound.const_mul 4) ?_
  · refine Filter.Eventually.of_forall fun n => ?_
    exact (((measurable_condMeanReflected hd v n).mul
      (measurable_levelDensity (fieldVar d v) _)).aestronglyMeasurable)
  · filter_upwards [eventually_condMeanReflected_mul_levelDensity_le hGaussConc hGH hd v hv hsq,
      hatt.eventually_gt_atTop 0] with n hb ha
    refine Filter.Eventually.of_forall fun y => ?_
    have hmnn : 0 ≤ condMeanReflected d hd v n y := condMeanReflected_nonneg hd v n y
    have hdnn : 0 ≤ levelDensity (fieldVar d v)
        (meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n) y :=
      levelDensity_nonneg _ ha y
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hmnn hdnn)]
    exact hb y
  · refine Filter.Eventually.of_forall fun y => ?_
    have h1 := tendsto_integral_condReflected_posPart hGH hd v hv hsq y
    have h2 := tendsto_levelDensity (fieldVar d v) hw hatt y
    have h := h1.mul h2
    exact h.congr fun n => rfl

/-- **`eq:dgt4-contact-mean-increment`** (`sandpile.tex:4976-4979`) in case (a). -/
theorem gaussianMeanIncrement_of
    (hGaussConc : Sandpile.External.GaussianLipschitzConcentration)
    (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    (v : ℝ≥0) (hv : v ≠ 0) (hsq : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 v)) :
    GaussianMeanIncrement d (gaussianReal 0 v) (fieldVar d v) := by
  have hGpos : (0 : ℝ) < green d 0 0 :=
    lt_of_lt_of_le zero_lt_one (Sandpile.one_le_green (by omega))
  have hw : fieldVar d v ≠ 0 := fieldVar_ne_zero hd hv
  have hSpos : (0 : ℝ) < ((fieldVar d v : ℝ≥0) : ℝ) := coe_pos_of_ne_zero hw
  have hatt := tendsto_meanOdometer_gaussian_atTop hGH hd v hv
  set S : ℝ := ((fieldVar d v : ℝ≥0) : ℝ) with hSdef
  set a : ℕ → ℝ := fun n => meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n with hadef
  set Δ : ℕ → ℝ := fun n => meanOdometer (centeredMassLaw d (gaussianReal 0 v)) (n + 1)
    - meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n with hΔ
  set b : ℕ → ℝ := fun n => gaussianUpperTail (fieldVar d v) (a n) with hbdef
  set I : ℕ → ℝ := fun n => gaussianIntegratedTail (fieldVar d v) (a n) with hIdef
  have hbpos : ∀ n, 0 < b n := fun n => gaussianUpperTail_pos _ hw _
  have hbnd : GaussianMillsBounds (fieldVar d v) := gaussianMillsBounds _ hw
  have hIpos : ∀ᶠ n : ℕ in atTop, 0 < I n := by
    filter_upwards [hatt.eventually_gt_atTop 0] with n hn
    refine lt_of_lt_of_le ?_ (hbnd.le_mean _ hn)
    have hpn := gaussianPDFReal_pos 0 (fieldVar d v) (a n) hw
    positivity
  -- the limit of the integral representation
  have hP : Tendsto (fun n : ℕ => a n / S * Δ n / b n) atTop (𝓝 (1 / green d 0 0)) := by
    have hmain := tendsto_integral_condMeanReflected_levelDensity hGaussConc hGH hd v hv hsq
    refine hmain.congr' ?_
    filter_upwards [hatt.eventually_gt_atTop 0] with n ha
    have hrep := integral_condMeanReflected_pdf hd v hv n ha
    have hld : ∀ z : ℝ, levelDensity (fieldVar d v) (a n) z
        = S / a n * gaussianPDFReal 0 (fieldVar d v) (a n + S * z / a n) / b n :=
      fun _ => rfl
    have hsplit : (∫ y : ℝ, condMeanReflected d hd v n y
        * levelDensity (fieldVar d v) (a n) y)
        = (∫ y : ℝ, S / a n * gaussianPDFReal 0 (fieldVar d v) (a n + S * y / a n)
            * condMeanReflected d hd v n y) / b n := by
      rw [← integral_div]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [hld]
      ring
    rw [hsplit, hrep]
  -- the Mills ratio for the integrated tail
  have hQ : Tendsto (fun n : ℕ => a n * I n / (S * b n)) atTop (𝓝 1) := by
    simpa [Function.comp_def] using (tendsto_gaussMills_mean (fieldVar d v) hw hbnd).comp hatt
  have hdiv := (hP.const_mul (green d 0 0)).div hQ one_ne_zero
  rw [mul_one_div, div_self (ne_of_gt hGpos), div_one] at hdiv
  refine hdiv.congr' ?_
  filter_upwards [hatt.eventually_gt_atTop 0, hIpos] with n ha hI
  have hbn := hbpos n
  have hane : a n ≠ 0 := ne_of_gt ha
  have hSne : S ≠ 0 := ne_of_gt hSpos
  have hbne : b n ≠ 0 := ne_of_gt hbn
  have hIne : I n ≠ 0 := ne_of_gt hI
  show green d 0 0 * (a n / S * Δ n / b n) / (a n * I n / (S * b n))
      = green d 0 0 * Δ n / I n
  field_simp


end Sandpile
