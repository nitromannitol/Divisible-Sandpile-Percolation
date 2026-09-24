/-
**The `y\leq-1` bound of Step 4 of case (a)**
(`eq:dgt4-gaussian-conditional-concentration`, `sandpile.tex:5267-5282`).

The paper bounds the conditional mean increment at a level far below the threshold by
concentration: "By `eq:dgt4-gaussian-terminal-domination`,
`-\zeta(0)-Pu_n(0)\leq yh_n+\Theta_n`. [...] The comparison in Step 2, now retaining the
dependence on `y`, gives, uniformly for `y\leq-1`,
`\E[|\Theta_n|\mid\cdot]\leq o(h_n)+Ck_n^{-(d-4)/2}(\E u_n(0)+|y|h_n)\leq|y|h_n/2`. [...]
Integrating the conditional concentration tail therefore gives
`m_n(y)\leq C\exp\{-cy^2k_n^{(d-4)/2}/(\E u_n(0))^2\}`."

Both halves are here.  The conditional mean of the terminal quantity at the level `y` is
bounded with the `y` dependence retained, which is the comparison of Step 2 read at an
unbounded level; and the mean excess inequality of `Support/Dgt4AStep4Tail.lean` turns the
conditional concentration tail into the bound on `m_n(y)`.  The exponent obtained is linear
in `|y|` rather than quadratic, which is all the domination of Step 4 needs, since the
coefficient tends to infinity.
-/
import Sandpile.Support.Dgt4AStep4Tail
import Sandpile.Support.Dgt4AStep4Rep

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}

/-- The `L^2` norm of the tail kernel at horizon `j` is at most `Cj^{(4-d)/4}`
(`eq:dgt4-tail-kernel`, `sandpile.tex:1303-1306`). -/
theorem exists_norm_tailKernelLp_le (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : ℕ) (hj : 1 ≤ j),
      ‖(tailKernelLp hGH hd hj : lp (fun _ : Site d => ℝ) 2)‖
        ≤ C * (j : ℝ) ^ ((4 - (d : ℝ)) / 4) := by
  obtain ⟨Ct, hCt, htail⟩ := (hGH d hd).2.2.1
  refine ⟨Real.sqrt Ct + 1, by positivity, fun j hj => ?_⟩
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have hroot : Real.sqrt ((j : ℝ) ^ ((4 - (d : ℝ)) / 2)) = (j : ℝ) ^ ((4 - (d : ℝ)) / 4) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hjpos.le]
    congr 1
    ring
  have hsq : ‖(tailKernelLp hGH hd hj : lp (fun _ : Site d => ℝ) 2)‖ ^ 2
      ≤ Ct * (j : ℝ) ^ ((4 - (d : ℝ)) / 2) := by
    rw [norm_tailKernelLp_sq hGH hd hj]
    exact (htail j hj).2.2
  have hle : ‖(tailKernelLp hGH hd hj : lp (fun _ : Site d => ℝ) 2)‖
      ≤ Real.sqrt (Ct * (j : ℝ) ^ ((4 - (d : ℝ)) / 2)) := by
    rw [show ‖(tailKernelLp hGH hd hj : lp (fun _ : Site d => ℝ) 2)‖
        = Real.sqrt (‖(tailKernelLp hGH hd hj : lp (fun _ : Site d => ℝ) 2)‖ ^ 2) from
      (Real.sqrt_sq (norm_nonneg _)).symm]
    exact Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_mul hCt.le, hroot] at hle
  have hjp : (0 : ℝ) ≤ (j : ℝ) ^ ((4 - (d : ℝ)) / 4) := Real.rpow_nonneg hjpos.le _
  nlinarith [hle, hjp, Real.sqrt_nonneg Ct]

/-- **The comparison of Step 2 with the dependence on the level retained**
(`sandpile.tex:5267-5272`): the scaled conditional mean of the terminal quantity at the
level `y` is at most a null sequence plus `Ck_n^{(4-d)/4}|y|`. -/
theorem exists_integral_condTerminal_condLevel_le (hGH : Sandpile.External.GreenBoundsHigh)
    (hd : 5 ≤ d) (v : ℝ≥0) (hv : v ≠ 0)
    (hsq : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 v)) :
    ∃ C : ℝ, 0 < C ∧ ∃ eps : ℕ → ℝ, Tendsto eps atTop (𝓝 0) ∧
      ∀ n : ℕ, 0 < meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n → ∀ y : ℝ,
        meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n / ((fieldVar d v : ℝ≥0) : ℝ)
            * (∫ r, condTerminal d hd (Real.sqrt (v : ℝ)) (condLevel d hd v y n)
                (meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n)
                (n - dgt4Horizon d n) (dgt4Horizon d n + 1) r
              ∂((LatticeProb.gaussLaw (Site d)).map (residField d hd)))
          ≤ eps n + C * ((dgt4Horizon d n + 1 : ℕ) : ℝ) ^ ((4 - (d : ℝ)) / 4) * |y| := by
  obtain ⟨C₀, hC₀, hcomp⟩ := exists_abs_integral_condTerminal_sub_le hGH hd
  set S : ℝ := ((fieldVar d v : ℝ≥0) : ℝ) with hSdef
  have hSpos : (0 : ℝ) < S := coe_pos_of_ne_zero (fieldVar_ne_zero hd hv)
  set N : ℝ := ‖greenLp d hd (0 : Site d)‖ with hNdef
  have hNpos : (0 : ℝ) < N := norm_greenLp_pos hd
  set cc : ℝ := Real.sqrt (v : ℝ) with hccdef
  have hccpos : (0 : ℝ) < cc := Real.sqrt_pos.2 (coe_pos_of_ne_zero hv)
  set M : ℝ := ∫ z, |z| ∂(gaussianReal 0 1) with hMdef
  have hMnn : (0 : ℝ) ≤ M := integral_nonneg fun z => abs_nonneg z
  set a : ℕ → ℝ := fun n => meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n with hadef
  have hann : ∀ n, (0 : ℝ) ≤ a n := fun n => meanOdometer_nonneg _ n
  set p : ℕ → ℝ := fun n => ((dgt4Horizon d n + 1 : ℕ) : ℝ) ^ ((4 - (d : ℝ)) / 4) with hpdef
  have hpnn : ∀ n, (0 : ℝ) ≤ p n := fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _
  set F : ℕ → ℝ := fun n => ∫ ζ, (avg^[dgt4Horizon d n + 1]
      (fun x => |infiniteGreenField ζ x - odometerOf ζ (n - dgt4Horizon d n) x + a n|)) 0
      ∂(LatticeProb.iidLaw d (gaussianReal 0 v)) with hFdef
  refine ⟨C₀, hC₀, fun n => a n / S * |F n| + C₀ * p n * (a n) ^ 2 / S
    + C₀ * N * cc * M * a n * p n / S, ?_, ?_⟩
  · have hF := tendsto_meanOdometer_mul_avgIterate_abs_centeredValue_horizon hGH hd v hv
    have hsq2 := tendsto_meanOdometer_sq_mul_horizon_rpow hGH hd v hv
    have hp0 := tendsto_horizon_rpow (d := d) hd
    have h1 : Tendsto (fun n : ℕ => a n / S * |F n|) atTop (𝓝 0) := by
      have h := (hF.abs).div_const S
      rw [abs_zero, zero_div] at h
      refine h.congr fun n => ?_
      rw [abs_mul, abs_of_nonneg (hann n)]
      ring
    have h2 : Tendsto (fun n : ℕ => C₀ * p n * (a n) ^ 2 / S) atTop (𝓝 0) := by
      have h := (hsq2.const_mul C₀).div_const S
      rw [mul_zero, zero_div] at h
      refine h.congr fun n => ?_
      ring
    have hap : Tendsto (fun n : ℕ => a n * p n) atTop (𝓝 0) := by
      refine squeeze_zero (fun n => mul_nonneg (hann n) (hpnn n)) (fun n => ?_)
        (by simpa only [add_zero] using hsq2.add hp0)
      have h1 : a n ≤ a n ^ 2 + 1 := by nlinarith [sq_nonneg (a n - 1)]
      calc a n * p n ≤ (a n ^ 2 + 1) * p n := mul_le_mul_of_nonneg_right h1 (hpnn n)
        _ = a n ^ 2 * p n + p n := by ring
    have h3 : Tendsto (fun n : ℕ => C₀ * N * cc * M * a n * p n / S) atTop (𝓝 0) := by
      have h := (hap.const_mul (C₀ * N * cc * M)).div_const S
      rw [mul_zero, zero_div] at h
      refine h.congr fun n => ?_
      ring
    have := (h1.add h2).add h3
    simpa using this
  · intro n ha y
    have hane : a n ≠ 0 := ne_of_gt ha
    have hk1 : 1 ≤ dgt4Horizon d n + 1 := Nat.succ_le_succ (Nat.zero_le _)
    have hb := hcomp v hsq (a n) (condLevel d hd v y n) (n - dgt4Horizon d n)
      (dgt4Horizon d n + 1) hk1
    rw [abs_of_nonneg hccpos.le] at hb
    have hbb := abs_le.1 hb
    have hlev : cc * N * |condLevel d hd v y n| ≤ a n + S * |y| / a n := by
      have hmul := condLevel_mul hd hv y n
      have habs : cc * |condLevel d hd v y n| * N = |a n + S * y / a n| := by
        have h := congrArg abs hmul
        rw [abs_neg] at h
        rw [← h, abs_mul, abs_mul, abs_of_pos hccpos, abs_of_pos hNpos]
      have hsplit : |a n + S * y / a n| ≤ a n + S * |y| / a n := by
        have h1 : |a n + S * y / a n| ≤ |a n| + |S * y / a n| := abs_add_le _ _
        rw [abs_of_nonneg (hann n), abs_div, abs_mul, abs_of_pos hSpos,
          abs_of_nonneg (hann n)] at h1
        exact h1
      calc cc * N * |condLevel d hd v y n| = cc * |condLevel d hd v y n| * N := by ring
        _ = |a n + S * y / a n| := habs
        _ ≤ a n + S * |y| / a n := hsplit
    have hkey : a n / S * (C₀ * N * p n * cc * (|condLevel d hd v y n| + M))
        ≤ C₀ * p n * (a n) ^ 2 / S + C₀ * p n * |y| + C₀ * N * cc * M * a n * p n / S := by
      have hmul := mul_le_mul_of_nonneg_left hlev
        (by positivity : (0 : ℝ) ≤ C₀ * p n * (a n / S))
      have hval : C₀ * p n * (a n / S) * (a n + S * |y| / a n)
          = C₀ * p n * (a n) ^ 2 / S + C₀ * p n * |y| := by
        field_simp
      rw [hval] at hmul
      have hrw : a n / S * (C₀ * N * p n * cc * (|condLevel d hd v y n| + M))
          = C₀ * p n * (a n / S) * (cc * N * |condLevel d hd v y n|)
            + C₀ * N * cc * M * a n * p n / S := by ring
      rw [hrw]
      linarith
    have hX : (∫ r, condTerminal d hd cc (condLevel d hd v y n) (a n)
        (n - dgt4Horizon d n) (dgt4Horizon d n + 1) r
        ∂((LatticeProb.gaussLaw (Site d)).map (residField d hd)))
        ≤ |F n| + C₀ * N * p n * cc * (|condLevel d hd v y n| + M) := by
      have := hbb.2
      have hFa : F n ≤ |F n| := le_abs_self _
      calc (∫ r, condTerminal d hd cc (condLevel d hd v y n) (a n)
            (n - dgt4Horizon d n) (dgt4Horizon d n + 1) r
            ∂((LatticeProb.gaussLaw (Site d)).map (residField d hd)))
          ≤ F n + C₀ * N * p n * cc * (|condLevel d hd v y n| + M) := by linarith
        _ ≤ |F n| + C₀ * N * p n * cc * (|condLevel d hd v y n| + M) := by linarith
    have hscale := mul_le_mul_of_nonneg_left hX (by positivity : (0 : ℝ) ≤ a n / S)
    rw [mul_add] at hscale
    linarith

/-- **The `y\leq-1` bound** (`eq:dgt4-gaussian-conditional-concentration`,
`sandpile.tex:5273-5277`): for all large `n` and every level `y\leq-1`, the scaled
conditional mean of the positive part of the reflected increment is at most `e^{-2|y|}`. -/
theorem eventually_integral_condReflected_posPart_le
    (hGaussConc : Sandpile.External.GaussianLipschitzConcentration)
    (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    (v : ℝ≥0) (hv : v ≠ 0) (hsq : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 v)) :
    ∀ᶠ n : ℕ in atTop, ∀ y : ℝ, y ≤ -1 →
      (∫ r, max (meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n
            / ((fieldVar d v : ℝ≥0) : ℝ)
          * condReflected d hd (Real.sqrt (v : ℝ)) (condLevel d hd v y n) n r) 0
        ∂((LatticeProb.gaussLaw (Site d)).map (residField d hd)))
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
    have : (0 : ℝ) ≤ cc * ‖(tailKernelLp hGH hd (hk1 n) : lp (fun _ : Site d => ℝ) 2)‖ :=
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
  have hlamval : ∀ m : ℕ, lam m = a m / S * Lam m := fun _ => rfl
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
    hlam0.eventually_le_const (by norm_num : (0:ℝ) < 1 / 4),
    heps.eventually_le_const (by norm_num : (0:ℝ) < 1 / 4),
    hCp.eventually_le_const (by norm_num : (0:ℝ) < 1 / 4)] with n ha hkle hlamn hepsn hCpn
  intro y hy
  have hane : a n ≠ 0 := ne_of_gt ha
  have hyneg : y < 0 := by linarith
  have hb : (1 : ℝ) ≤ |y| := by rw [abs_of_neg hyneg]; linarith
  set b : ℝ := |y| with hbdef
  have hby : y = -b := by rw [hbdef, abs_of_neg hyneg]; ring
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
  have hWint : Integrable W ρ := hThint.const_mul kap
  have hWmean : (∫ r, W r ∂ρ) = kap * ∫ r, Th r ∂ρ := integral_const_mul _ _
  -- the mean of `W` is at most half the level
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
  -- the conditional concentration tail
  have htail : ∀ τ : ℝ, 0 ≤ τ →
      (ρ {r | (∫ r', W r' ∂ρ) + τ ≤ W r}).toReal ≤ Real.exp (-(τ ^ 2) / (2 * lam n ^ 2)) := by
    intro τ hτ
    have hset : {r | (∫ r', W r' ∂ρ) + τ ≤ W r}
        = {r | (∫ r', Th r' ∂ρ) + τ / kap ≤ Th r} := by
      ext r
      simp only [Set.mem_setOf_eq]
      constructor
      · intro h
        rw [hWmean] at h
        have hWr : W r = kap * Th r := rfl
        rw [hWr] at h
        have he : (∫ r', Th r' ∂ρ) + τ / kap = (kap * (∫ r', Th r' ∂ρ) + τ) / kap := by
          field_simp
        rw [he, div_le_iff₀ hkappos]
        linarith
      · intro h
        have hmul := mul_le_mul_of_nonneg_left h hkappos.le
        have he : kap * ((∫ r', Th r' ∂ρ) + τ / kap) = kap * (∫ r', Th r' ∂ρ) + τ := by
          field_simp
        rw [he] at hmul
        rw [hWmean]
        exact hmul
    have hconc := measure_resid_condTheta_ge_le_gauss hGaussConc hGH hd v hsq s (a n)
      (n - dgt4Horizon d n) (dgt4Horizon d n + 1) (hk1 n) (Lam n) (hLampos n)
      (by rw [hLamdef]; linarith [hppos n]) (τ / kap) (div_nonneg hτ hkappos.le)
    rw [hset]
    have hmono := ENNReal.toReal_mono (by finiteness) hconc
    rw [ENNReal.toReal_ofReal (Real.exp_nonneg _)] at hmono
    refine le_trans hmono (le_of_eq ?_)
    congr 1
    have hlv : lam n = kap * Lam n := by rw [hlamval n]
    rw [hlv]
    have hLne : Lam n ≠ 0 := ne_of_gt (hLampos n)
    have hkne : kap ≠ 0 := ne_of_gt hkappos
    field_simp
  have hlampos : (0 : ℝ) < lam n := by
    rw [hlamval n, ← hkapval]
    exact mul_pos hkappos (hLampos n)
  have hexc := integral_posPart_sub_le_of_conc ρ W hWint (lam n) b hlampos hb hmean htail
  -- the excess bound is below `e^{-2|y|}`
  have hlam2 : lam n ^ 2 ≤ 1 / 16 := by nlinarith [hlampos, hlamn]
  have hfac : 4 * lam n ^ 2 ≤ 1 / 4 := by linarith
  have hexpo : Real.exp (-(b / (8 * lam n ^ 2))) ≤ Real.exp (-(2 * b)) := by
    refine Real.exp_le_exp.2 ?_
    have h8 : (0 : ℝ) < 8 * lam n ^ 2 := by positivity
    rw [neg_le_neg_iff, le_div_iff₀ h8]
    nlinarith [hb, hlam2]
  have hfinal : 4 * lam n ^ 2 * Real.exp (-(b / (8 * lam n ^ 2))) ≤ Real.exp (-(2 * b)) := by
    have h1 : 4 * lam n ^ 2 * Real.exp (-(b / (8 * lam n ^ 2)))
        ≤ 4 * lam n ^ 2 * Real.exp (-(2 * b)) :=
      mul_le_mul_of_nonneg_left hexpo (by positivity)
    nlinarith [Real.exp_pos (-(2 * b)), hfac]
  -- compare the positive part of the reflected increment with the excess
  have hcomparison : (∫ r, max (kap * condReflected d hd cc s n r) 0 ∂ρ)
      ≤ ∫ r, max (W r - b) 0 ∂ρ := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun r => le_max_right _ _)
      ((hWint.sub (integrable_const b)).pos_part) ?_
    filter_upwards [ae_mem_condConv hd cc s, ae_infiniteGreenField_condLevel hd hv y n]
      with r hr hlev
    refine max_le_max ?_ le_rfl
    have hdom := condReflected_le hd cc s (a n) S y (dgt4Horizon d n) n hkle r hr hlev
    have h := mul_le_mul_of_nonneg_left hdom hkappos.le
    have hval : kap * (S * y / a n) = y := by
      rw [hkapval]
      field_simp
    rw [mul_add, hval] at h
    rw [hWdef, hThdef]
    rw [hby] at h
    linarith
  calc (∫ r, max (kap * condReflected d hd cc s n r) 0 ∂ρ)
      ≤ ∫ r, max (W r - b) 0 ∂ρ := hcomparison
    _ ≤ 4 * lam n ^ 2 * Real.exp (-(b / (8 * lam n ^ 2))) := hexc
    _ ≤ Real.exp (-(2 * b)) := hfinal

end Sandpile
