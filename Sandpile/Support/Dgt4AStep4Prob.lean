/-
**The conditional contact probability of Step 4 of case (a)**
(`eq:dgt4-gaussian-conditional-contact`, `sandpile.tex:5141-5147` and
`sandpile.tex:5283-5286`).

The contact event is `\{u_{n+1}(0)=0\}=\{-\zeta(0)-Pu_n(0)\geq0\}`, with a wide inequality:
the odometer recursion is `u_{n+1}(0)=(\zeta(0)+Pu_n(0))_+`.  Step 3 gives the limit of the
conditional probability of the STRICT event, so the wide one is read off it for `y>0` by
monotonicity, and for `y<0` by the same comparison, which bounds the wide event as well.
The paper's sentence "The same bound holds with `m_n(y)` replaced by the conditional
probability" is the second theorem: on the contact event the terminal quantity exceeds
`\Sigma^2|y|/\E u_n(0)`, so the conditional concentration tail bounds the conditional
probability by `e^{-2|y|}` for `y\leq-1` and all large `n`.
-/
import Sandpile.Support.Dgt4AStep4Mean

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace Sandpile

variable {α : Type*} [MeasurableSpace α]

/-- The wide form of the comparison of Step 3 at a negative limit: if `X` is within `T` of a
negative `L` off an exceptional set, the event `\{X\geq0\}` is small. -/
theorem measure_nonneg_le (μ : Measure α) [IsProbabilityMeasure μ]
    (X T : α → ℝ) (B : Set α) (L : ℝ) (hL : L < 0)
    (hT0 : ∀ a, 0 ≤ T a) (hTint : Integrable T μ)
    (hcomp : ∀ a ∈ B, |X a - L| ≤ T a) :
    (μ {a | 0 ≤ X a}).toReal ≤ (μ Bᶜ).toReal + (∫ a, T a ∂μ) / |L| := by
  have hLpos : 0 < |L| := abs_pos.mpr (ne_of_lt hL)
  have hsub : {a | 0 ≤ X a} ⊆ Bᶜ ∪ {a | |L| ≤ T a} := by
    intro a ha
    by_cases hb : a ∈ B
    · refine Or.inr ?_
      have h0 : (0 : ℝ) ≤ X a := ha
      have hbig : |L| ≤ |X a - L| := by
        rw [abs_of_neg hL]
        have hstep : -L ≤ X a - L := by linarith
        exact le_trans hstep (le_abs_self _)
      exact le_trans hbig (hcomp a hb)
    · exact Or.inl hb
  have hne : μ Bᶜ + μ {a | |L| ≤ T a} ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩
  have hmono : (μ {a | 0 ≤ X a}).toReal ≤ (μ Bᶜ).toReal + (μ {a | |L| ≤ T a}).toReal := by
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    exact ENNReal.toReal_mono hne (le_trans (measure_mono hsub) (measure_union_le _ _))
  have hmark := measure_ge_le_integral_div μ T hT0 hTint hLpos
  linarith

variable {d : ℕ}

/-- **The conditional contact probability at a level below the threshold vanishes**
(`eq:dgt4-gaussian-conditional-contact` for `y<0`). -/
theorem tendsto_measure_condReflected_nonneg_neg
    (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d) (v : ℝ≥0) (hv : v ≠ 0)
    (hsq : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 v)) {y : ℝ} (hy : y < 0) :
    Tendsto (fun n : ℕ => (((LatticeProb.gaussLaw (Site d)).map (residField d hd))
        {r | 0 ≤ condReflected d hd (Real.sqrt (v : ℝ)) (condLevel d hd v y n) n r}).toReal)
      atTop (𝓝 0) := by
  set ρ : Measure (Site d → ℝ) :=
    (LatticeProb.gaussLaw (Site d)).map (residField d hd) with hρ
  haveI : IsProbabilityMeasure ρ := by
    rw [hρ]
    exact Measure.isProbabilityMeasure_map (measurable_residField hd).aemeasurable
  set cc : ℝ := Real.sqrt (v : ℝ) with hcc
  set S : ℝ := ((fieldVar d v : ℝ≥0) : ℝ) with hSdef
  have hSpos : (0 : ℝ) < S := coe_pos_of_ne_zero (fieldVar_ne_zero hd hv)
  set a : ℕ → ℝ := fun n => meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n with hadef
  set X : ℕ → (Site d → ℝ) → ℝ := fun n r =>
    a n / S * condReflected d hd cc (condLevel d hd v y n) n r with hXdef
  set T : ℕ → (Site d → ℝ) → ℝ := fun n r =>
    a n / S * condTerminal d hd cc (condLevel d hd v y n) (a n)
      (n - dgt4Horizon d n) (dgt4Horizon d n + 1) r with hTdef
  set mu : ℕ → ℝ := fun n => y - avg (LatticeProb.srwHitBy d (dgt4Horizon d n)) 0 * max y 0
    with hmudef
  have hmuval : ∀ n : ℕ, mu n = y := by
    intro n
    show y - avg (LatticeProb.srwHitBy d (dgt4Horizon d n)) 0 * max y 0 = y
    rw [max_eq_right hy.le, mul_zero, sub_zero]
  have hkkatt : Tendsto (fun n : ℕ => dgt4Horizon d n) atTop atTop :=
    tendsto_dgt4Horizon_atTop hd
  have hbad : Tendsto (fun n : ℕ => (ρ (condGood d hd v y n)ᶜ).toReal) atTop (𝓝 0) :=
    squeeze_zero' (Filter.Eventually.of_forall fun n => ENNReal.toReal_nonneg)
      (Filter.Eventually.of_forall fun n => measure_compl_condGood_le hd hv y n)
      (tendsto_measure_condBad hGH hd v hv (K := |y|) le_rfl)
  have hT : Tendsto (fun n : ℕ => ∫ r, T n r ∂ρ) atTop (𝓝 0) := by
    have hmain := tendsto_meanOdometer_mul_integral_condTerminal_condLevel hGH hd v hv hsq y
    have hdiv := hmain.div_const S
    rw [zero_div] at hdiv
    refine hdiv.congr fun n => ?_
    rw [hTdef, integral_const_mul]
    ring
  have hatt := tendsto_meanOdometer_gaussian_atTop hGH hd v hv
  have herr : Tendsto (fun n : ℕ =>
      (ρ (condGood d hd v y n)ᶜ).toReal + (∫ r, T n r ∂ρ) / |y|) atTop (𝓝 0) := by
    have h := hbad.add (hT.div_const |y|)
    simpa using h
  refine squeeze_zero' (Filter.Eventually.of_forall fun n => ENNReal.toReal_nonneg) ?_ herr
  filter_upwards [hatt.eventually_gt_atTop 0, eventually_dgt4Horizon_le hd] with n ha hkle
  have hTnn : ∀ r, 0 ≤ T n r := fun r =>
    mul_nonneg (div_nonneg ha.le hSpos.le)
      (condTerminal_nonneg hd cc (condLevel d hd v y n) (a n) (n - dgt4Horizon d n)
        (dgt4Horizon d n + 1) r)
  have hTint : Integrable (T n) ρ :=
    (integrable_condTerminal hGH hd v hsq (a n) (n - dgt4Horizon d n)
      (dgt4Horizon d n + 1) (by omega) (condLevel d hd v y n)).const_mul _
  have hcomp : ∀ r ∈ condGood d hd v y n, |X n r - mu n| ≤ T n r := by
    intro r hr
    obtain ⟨⟨hbad', hconv'⟩, hlev'⟩ := hr
    have h := abs_condReflected_sub_le hd cc (condLevel d hd v y n) (a n) S y hSpos ha
      (dgt4Horizon d n) (n - dgt4Horizon d n) r hconv' hlev'
      (good_of_notMem_condBad hd v y n hbad')
    rwa [show n - dgt4Horizon d n + dgt4Horizon d n = n from by omega] at h
  have hbnd := measure_nonneg_le ρ (X n) (T n) (condGood d hd v y n) (mu n)
    (by rw [hmuval n]; exact hy) hTnn hTint hcomp
  have hac : (0 : ℝ) < a n / S := div_pos ha hSpos
  have hset : {r | 0 ≤ X n r}
      = {r | 0 ≤ condReflected d hd cc (condLevel d hd v y n) n r} := by
    ext r
    simp only [Set.mem_setOf_eq, hXdef]
    constructor
    · intro h
      by_contra hcon
      nlinarith [hac, not_le.mp hcon]
    · intro h
      exact mul_nonneg hac.le h
  rw [hset, hmuval n] at hbnd
  exact hbnd

/-- **The conditional contact probability converges to the indicator of `\{y>0\}`**
(`eq:dgt4-gaussian-conditional-contact`, `sandpile.tex:5136-5142`), in the wide form that
the contact event `\{u_{n+1}(0)=0\}` has. -/
theorem tendsto_measure_condReflected_nonneg
    (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d) (v : ℝ≥0) (hv : v ≠ 0)
    (hsq : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 v)) {y : ℝ} (hy : y ≠ 0) :
    Tendsto (fun n : ℕ => (((LatticeProb.gaussLaw (Site d)).map (residField d hd))
        {r | 0 ≤ condReflected d hd (Real.sqrt (v : ℝ)) (condLevel d hd v y n) n r}).toReal)
      atTop (𝓝 (if 0 < y then 1 else 0)) := by
  set ρ : Measure (Site d → ℝ) :=
    (LatticeProb.gaussLaw (Site d)).map (residField d hd) with hρ
  haveI : IsProbabilityMeasure ρ := by
    rw [hρ]
    exact Measure.isProbabilityMeasure_map (measurable_residField hd).aemeasurable
  rcases hy.lt_or_gt with hneg | hpos
  · rw [if_neg (by linarith)]
    exact tendsto_measure_condReflected_nonneg_neg hGH hd v hv hsq hneg
  · rw [if_pos hpos]
    have hstrict := tendsto_measure_condReflected_pos hGH hd v hv hsq hy
    rw [if_pos hpos] at hstrict
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hstrict
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)) (fun n => ?_)
      (fun n => ?_)
    · refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_)
      intro r hr
      have h : 0 < condReflected d hd (Real.sqrt (v : ℝ)) (condLevel d hd v y n) n r := hr
      exact le_of_lt h
    · have h := prob_le_one (μ := ρ)
        (s := {r | 0 ≤ condReflected d hd (Real.sqrt (v : ℝ)) (condLevel d hd v y n) n r})
      exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simpa using h)

/-- **The `y\leq-1` bound for the conditional contact probability**
(`sandpile.tex:5278-5279`): "The same bound holds with `m_n(y)` replaced by the conditional
probability." -/
theorem eventually_measure_condReflected_nonneg_le
    (hGaussConc : Sandpile.External.GaussianLipschitzConcentration)
    (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    (v : ℝ≥0) (hv : v ≠ 0) (hsq : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 v)) :
    ∀ᶠ n : ℕ in atTop, ∀ y : ℝ, y ≤ -1 →
      (((LatticeProb.gaussLaw (Site d)).map (residField d hd))
        {r | 0 ≤ condReflected d hd (Real.sqrt (v : ℝ)) (condLevel d hd v y n) n r}).toReal
        ≤ Real.exp (-(2 * |y|)) := by
  set ρ : Measure (Site d → ℝ) :=
    (LatticeProb.gaussLaw (Site d)).map (residField d hd) with hρ
  haveI : IsProbabilityMeasure ρ := by
    rw [hρ]
    exact Measure.isProbabilityMeasure_map (measurable_residField hd).aemeasurable
  set S : ℝ := ((fieldVar d v : ℝ≥0) : ℝ) with hSdef
  have hSpos : (0 : ℝ) < S := coe_pos_of_ne_zero (fieldVar_ne_zero hd hv)
  have hSne : S ≠ 0 := ne_of_gt hSpos
  set cc : ℝ := Real.sqrt (v : ℝ) with hccdef
  have hccpos : (0 : ℝ) < cc := Real.sqrt_pos.2 (coe_pos_of_ne_zero hv)
  set a : ℕ → ℝ := fun n => meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n with hadef
  set p : ℕ → ℝ := fun n => ((dgt4Horizon d n + 1 : ℕ) : ℝ) ^ ((4 - (d : ℝ)) / 4) with hpdef
  have hppos : ∀ n, (0 : ℝ) < p n := fun n =>
    Real.rpow_pos_of_pos (by exact_mod_cast Nat.succ_pos _) _
  have hk1 : ∀ n : ℕ, 1 ≤ dgt4Horizon d n + 1 := fun _ => Nat.succ_le_succ (Nat.zero_le _)
  obtain ⟨C₁, hC₁, hnorm⟩ := exists_norm_tailKernelLp_le hGH hd
  obtain ⟨C₂, hC₂, eps, heps, hterm⟩ := exists_integral_condTerminal_condLevel_le hGH hd v hv hsq
  set Lam : ℕ → ℝ := fun n =>
    cc * ‖(tailKernelLp hGH hd (hk1 n) : lp (fun _ : Site d => ℝ) 2)‖ + p n with hLamdef
  have hLampos : ∀ n, (0 : ℝ) < Lam n := fun n => by
    have h : (0 : ℝ) ≤ cc * ‖(tailKernelLp hGH hd (hk1 n) : lp (fun _ : Site d => ℝ) 2)‖ :=
      mul_nonneg hccpos.le (norm_nonneg _)
    rw [hLamdef]
    linarith [hppos n]
  have hLamle : ∀ n, Lam n ≤ (cc * C₁ + 1) * p n := fun n => by
    have h := hnorm (dgt4Horizon d n + 1) (hk1 n)
    have h2 : cc * ‖(tailKernelLp hGH hd (hk1 n) : lp (fun _ : Site d => ℝ) 2)‖
        ≤ cc * (C₁ * p n) := mul_le_mul_of_nonneg_left h hccpos.le
    rw [hLamdef]
    nlinarith [h2]
  set lam : ℕ → ℝ := fun n => a n / S * Lam n with hlamdef
  have hlamval : ∀ m : ℕ, lam m = a m / S * Lam m := fun _ => rfl
  have hatt := tendsto_meanOdometer_gaussian_atTop hGH hd v hv
  have hap : Tendsto (fun n : ℕ => a n * p n) atTop (𝓝 0) := by
    have hsq2 := tendsto_meanOdometer_sq_mul_horizon_rpow hGH hd v hv
    have hp0 := tendsto_horizon_rpow (d := d) hd
    refine squeeze_zero (fun n => mul_nonneg (meanOdometer_nonneg _ n) (hppos n).le)
      (fun n => ?_) (by simpa only [add_zero] using hsq2.add hp0)
    have h1 : a n ≤ a n ^ 2 + 1 := by
      nlinarith [sq_nonneg (a n - 1), meanOdometer_nonneg (d := d) (gaussianReal 0 v) n]
    calc a n * p n ≤ (a n ^ 2 + 1) * p n := mul_le_mul_of_nonneg_right h1 (hppos n).le
      _ = a n ^ 2 * p n + p n := by ring
  have hlam0 : Tendsto lam atTop (𝓝 0) := by
    refine squeeze_zero (fun n => by
      rw [hlamval n]
      exact mul_nonneg (div_nonneg (meanOdometer_nonneg _ n) hSpos.le) (hLampos n).le)
      (fun n => ?_) (show Tendsto (fun n : ℕ => (cc * C₁ + 1) / S * (a n * p n))
        atTop (𝓝 0) by simpa only [mul_zero] using (hap.const_mul ((cc * C₁ + 1) / S)))
    have h := mul_le_mul_of_nonneg_left (hLamle n)
      (div_nonneg (meanOdometer_nonneg (d := d) (gaussianReal 0 v) n) hSpos.le)
    rw [hlamval n]
    calc a n / S * Lam n ≤ a n / S * ((cc * C₁ + 1) * p n) := h
      _ = (cc * C₁ + 1) / S * (a n * p n) := by ring
  have hCp : Tendsto (fun n : ℕ => C₂ * p n) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_horizon_rpow (d := d) hd).const_mul C₂
  filter_upwards [hatt.eventually_gt_atTop 0, eventually_dgt4Horizon_le hd,
    hlam0.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 4),
    heps.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 4),
    hCp.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 4)] with n ha hkle hlamn hepsn hCpn
  intro y hy
  have hane : a n ≠ 0 := ne_of_gt ha
  have hyneg : y < 0 := by linarith
  have hb : (1 : ℝ) ≤ |y| := by rw [abs_of_neg hyneg]; linarith
  set b : ℝ := |y| with hbdef
  set kap : ℝ := a n / S with hkapdef
  have hkapval : kap = a n / S := rfl
  have hkappos : (0 : ℝ) < kap := div_pos ha hSpos
  set s : ℝ := condLevel d hd v y n with hsdef
  set Th : (Site d → ℝ) → ℝ :=
    condTheta d hd cc s (a n) (n - dgt4Horizon d n) (dgt4Horizon d n + 1) with hThdef
  set W : (Site d → ℝ) → ℝ := fun r => kap * Th r with hWdef
  have hThint : Integrable Th ρ :=
    integrable_condTheta hGH hd v hsq (a n) (n - dgt4Horizon d n) (dgt4Horizon d n + 1)
      (hk1 n) s
  have hWmean : (∫ r, W r ∂ρ) = kap * ∫ r, Th r ∂ρ := integral_const_mul _ _
  have hTle : (∫ r, Th r ∂ρ)
      ≤ ∫ r, condTerminal d hd cc s (a n) (n - dgt4Horizon d n) (dgt4Horizon d n + 1) r ∂ρ := by
    refine integral_mono hThint
      (integrable_condTerminal hGH hd v hsq (a n) (n - dgt4Horizon d n)
        (dgt4Horizon d n + 1) (hk1 n) s) fun r => ?_
    exact le_trans (le_abs_self _)
      (abs_condTheta_le_condTerminal hd cc s (a n) (n - dgt4Horizon d n)
        (dgt4Horizon d n + 1) r)
  have hmean : (∫ r, W r ∂ρ) ≤ b / 2 := by
    have h1 := hterm n ha y
    have h2 : kap * (∫ r, Th r ∂ρ) ≤ eps n + C₂ * p n * b :=
      le_trans (mul_le_mul_of_nonneg_left hTle hkappos.le) h1
    have h3 : C₂ * p n * b ≤ b / 4 := by nlinarith [hCpn, hb]
    rw [hWmean]
    linarith
  have hlampos : (0 : ℝ) < lam n := by
    rw [hlamval n, ← hkapval]
    exact mul_pos hkappos (hLampos n)
  -- the contact event forces `W` above `b`
  have hincl : ρ {r | 0 ≤ condReflected d hd cc s n r} ≤ ρ {r | b ≤ W r} := by
    refine measure_mono_ae ?_
    filter_upwards [ae_mem_condConv hd cc s, ae_infiniteGreenField_condLevel hd hv y n]
      with r hr hlev hmem
    have hpos : 0 ≤ condReflected d hd cc s n r := hmem
    have hdom := condReflected_le hd cc s (a n) S y (dgt4Horizon d n) n hkle r hr hlev
    have h := mul_le_mul_of_nonneg_left hdom hkappos.le
    have hval : kap * (S * y / a n) = y := by
      rw [hkapval]
      field_simp
    rw [mul_add, hval] at h
    have hzero : (0 : ℝ) ≤ kap * condReflected d hd cc s n r := mul_nonneg hkappos.le hpos
    show b ≤ kap * Th r
    have hby : y = -b := by rw [hbdef, abs_of_neg hyneg]; ring
    rw [hby] at h
    rw [hWdef, hThdef] at *
    linarith
  -- the concentration tail at `b`
  have htail : ρ {r | (∫ r', W r' ∂ρ) + b / 2 ≤ W r}
      ≤ ENNReal.ofReal (Real.exp (-((b / 2) ^ 2) / (2 * lam n ^ 2))) := by
    have hset : {r | (∫ r', W r' ∂ρ) + b / 2 ≤ W r}
        = {r | (∫ r', Th r' ∂ρ) + (b / 2) / kap ≤ Th r} := by
      ext r
      simp only [Set.mem_setOf_eq]
      constructor
      · intro h
        rw [hWmean] at h
        have hWr : W r = kap * Th r := rfl
        rw [hWr] at h
        have he : (∫ r', Th r' ∂ρ) + (b / 2) / kap
            = (kap * (∫ r', Th r' ∂ρ) + b / 2) / kap := by field_simp
        rw [he, div_le_iff₀ hkappos]
        linarith
      · intro h
        have hmul := mul_le_mul_of_nonneg_left h hkappos.le
        have he : kap * ((∫ r', Th r' ∂ρ) + (b / 2) / kap)
            = kap * (∫ r', Th r' ∂ρ) + b / 2 := by field_simp
        rw [he] at hmul
        rw [hWmean]
        exact hmul
    have hconc := measure_resid_condTheta_ge_le_gauss hGaussConc hGH hd v hsq s (a n)
      (n - dgt4Horizon d n) (dgt4Horizon d n + 1) (hk1 n) (Lam n) (hLampos n)
      (by rw [hLamdef]; linarith [hppos n]) ((b / 2) / kap)
      (div_nonneg (by linarith) hkappos.le)
    rw [hset]
    refine le_trans hconc (le_of_eq ?_)
    congr 1
    have hlv : lam n = kap * Lam n := by rw [hlamval n]
    rw [hlv]
    have hLne : Lam n ≠ 0 := ne_of_gt (hLampos n)
    have hkne : kap ≠ 0 := ne_of_gt hkappos
    field_simp
  have hsub2 : {r | b ≤ W r} ⊆ {r | (∫ r', W r' ∂ρ) + b / 2 ≤ W r} := by
    intro r hr
    have h : b ≤ W r := hr
    show (∫ r', W r' ∂ρ) + b / 2 ≤ W r
    linarith [hmean]
  have hfinal : (ρ {r | 0 ≤ condReflected d hd cc s n r}).toReal
      ≤ Real.exp (-((b / 2) ^ 2) / (2 * lam n ^ 2)) := by
    have hle := le_trans hincl (le_trans (measure_mono hsub2) htail)
    have h := ENNReal.toReal_mono (by finiteness) hle
    rwa [ENNReal.toReal_ofReal (Real.exp_nonneg _)] at h
  have hlam2 : lam n ^ 2 ≤ 1 / 16 := by nlinarith [hlampos, hlamn]
  have hexpo : Real.exp (-((b / 2) ^ 2) / (2 * lam n ^ 2)) ≤ Real.exp (-(2 * b)) := by
    refine Real.exp_le_exp.2 ?_
    have h2 : (0 : ℝ) < 2 * lam n ^ 2 := by positivity
    rw [div_le_iff₀ h2]
    nlinarith [hb, hlam2, hlampos]
  calc (ρ {r | 0 ≤ condReflected d hd cc s n r}).toReal
      ≤ Real.exp (-((b / 2) ^ 2) / (2 * lam n ^ 2)) := hfinal
    _ ≤ Real.exp (-(2 * b)) := hexpo

end Sandpile
