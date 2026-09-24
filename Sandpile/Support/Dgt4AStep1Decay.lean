/-
`eq:dgt4-centered-value-decay` (`sandpile.tex:5031-5034`), the conclusion of Step 1 of case
(a) of `prop:dgt4-contact-asymptotics`, at the horizon `j=\lceil n^{1/d}\rceil`.

The three terms of `Support/Dgt4AStep1.lean` are bounded by

  `j^2\E[D_n^2]\leq4n^{2/d}(2\E u_n(0)+M)n^{-2/3}`,
  `\E[(P^jV_\infty(0))^2]\leq Cn^{(4-d)/(2d)}`,
  `\Var(P^ju_n(0))\leq Cn^{(4-d)/(2d)}`,

and `(4-d)/(2d)=2/d-1/2` is exactly the exponent the first term produces once the growth
`\E u_n(0)\leq K\sqrt{\log n}` of `eq:dgt4-gaussian-height-order` (`sandpile.tex:5035-5037`)
is absorbed into `n^{1/6}`.  The `1/6` of slack is what the interpolation `T=n^{1/3}` of
`Support/Dgt4AL2Cube.lean` buys in place of the paper's Gaussian concentration.
-/
import Sandpile.Support.Dgt4AStep1

open LatticeProb

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace Sandpile

/-- `\sqrt{\log x}\leq 2x^{1/6}` for `x\geq1`. -/
theorem sqrt_log_le_rpow_sixth (x : ℝ) (hx : 1 ≤ x) :
    Real.sqrt (Real.log x) ≤ 2 * x ^ ((1 : ℝ) / 6) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hc : (0 : ℝ) < x ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hx0 _
  have hlog3 : Real.log x = 3 * Real.log (x ^ ((1 : ℝ) / 3)) := by
    rw [Real.log_rpow hx0]
    ring
  have hle : Real.log (x ^ ((1 : ℝ) / 3)) ≤ x ^ ((1 : ℝ) / 3) - 1 :=
    Real.log_le_sub_one_of_pos hc
  have hlogle : Real.log x ≤ 3 * x ^ ((1 : ℝ) / 3) := by
    rw [hlog3]; linarith
  have hfac : Real.sqrt (3 * x ^ ((1 : ℝ) / 3)) = Real.sqrt 3 * x ^ ((1 : ℝ) / 6) := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3)]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le]
    norm_num
  have h3 : Real.sqrt 3 ≤ 2 := by
    have h4 : Real.sqrt 3 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
    have : Real.sqrt 4 = 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    linarith [h4, this.le, this.ge]
  have hxpow : (0 : ℝ) ≤ x ^ ((1 : ℝ) / 6) := Real.rpow_nonneg hx0.le _
  calc Real.sqrt (Real.log x) ≤ Real.sqrt (3 * x ^ ((1 : ℝ) / 3)) := Real.sqrt_le_sqrt hlogle
    _ = Real.sqrt 3 * x ^ ((1 : ℝ) / 6) := hfac
    _ ≤ 2 * x ^ ((1 : ℝ) / 6) := by nlinarith

variable {d : ℕ}

/-- **`eq:dgt4-centered-value-decay`** (`sandpile.tex:5026-5029`), in its squared form, with
the growth `\E u_n(0)\leq K\sqrt{\log n}` of `eq:dgt4-gaussian-height-order`
(`sandpile.tex:5030-5032`) as the input Step 1 takes from
`prop:dgt4-height-lower-stretched` and `thm:dgt4-height-upper-tail`.  The horizon is
`j=\lceil n^{1/d}\rceil`, and `(4-d)/(2d)=2/d-1/2` is exactly the exponent that the
telescoping produces. -/
theorem exists_integral_centeredValue_sq_le_decay
    (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d) (v : ℝ≥0)
    (hgrow : ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 2 ≤ n →
      meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n ≤ K * Real.sqrt (Real.log n)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (∫ ζ, (infiniteGreenField ζ 0 - odometerOf ζ n 0
            + meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n) ^ 2
          ∂(LatticeProb.iidLaw d (gaussianReal 0 v)))
        ≤ C * (n : ℝ) ^ ((4 - (d : ℝ)) / (2 * d)) := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hdR : (5 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
  set ν : Measure ℝ := gaussianReal 0 v with hν
  haveI : IsProbabilityMeasure ν := by rw [hν]; infer_instance
  set μ : Measure (Site d → ℝ) := LatticeProb.iidLaw d ν with hμ
  -- moments of the Gaussian one-site law
  have hintid : Integrable (id : ℝ → ℝ) ν :=
    memLp_one_iff_integrable.mp (by simpa using memLp_id_gaussianReal (μ := 0) (v := v) 1)
  have hmean : (∫ z, z ∂ν) = 0 := by
    rw [hν]
    exact ProbabilityTheory.integral_id_gaussianReal
  have hpos : Integrable (fun z : ℝ => max z 0) ν :=
    Integrable.mono' hintid.abs (measurable_id.max measurable_const).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right z 0)]
        exact max_le (le_abs_self z) (abs_nonneg z))
  have hsq2 : Integrable (fun z : ℝ => z ^ 2) ν := by
    have := (memLp_id_gaussianReal (μ := 0) (v := v) 2).integrable_sq
    simpa using this
  have hsqabs : Integrable (fun z : ℝ => |z| ^ (2 : ℝ)) ν := integrable_abs_rpow_two ν hsq2
  have hmom4 : Integrable (fun z : ℝ => |z| ^ (4 : ℝ)) ν := by
    have h := (memLp_id_gaussianReal (μ := 0) (v := v) 4).integrable_norm_rpow
      (by simp) (by simp)
    simpa [Real.norm_eq_abs] using h
  have hintD : ∀ n : ℕ, Integrable (fun ζ : Site d → ℝ => sceneryDeviation d ζ n ^ 2) μ := by
    intro n
    have h := integrable_abs_rpow_sceneryDeviation hd ν (p := (2 : ℝ)) (by norm_num) hsqabs n
    refine h.congr (Filter.Eventually.of_forall fun ζ => ?_)
    show |sceneryDeviation d ζ n| ^ (2 : ℝ) = sceneryDeviation d ζ n ^ 2
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  obtain ⟨K, hK, hKn⟩ := hgrow
  obtain ⟨M, hM⟩ := exists_integral_sceneryDeviation_sq_le_cube hd ν hintid hmean hpos hsqabs hmom4
  obtain ⟨CB, hCB, hBb⟩ := exists_integral_avgIterate_infiniteGreenField_sq_le hGH hd v
  obtain ⟨CC, hCC, hCb⟩ := exists_integral_avgIterate_odometerOf_sq_le hGH hd ν hsqabs
  set M' : ℝ := |M| + 1 with hM'
  set CC' : ℝ := CC * pairMoment ν 2 with hCC'
  have hM'pos : 0 < M' := by positivity
  have hCC'nonneg : 0 ≤ CC' := mul_nonneg hCC.le (pairMoment_nonneg ν 2)
  refine ⟨12 * (4 * K + M') + 3 * (CB + CC') + 1, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn1 : 1 ≤ n := by omega
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  set x : ℝ := (n : ℝ) ^ ((1 : ℝ) / d) with hxdef
  have hx1 : (1 : ℝ) ≤ x := Real.one_le_rpow hnR (by positivity)
  have hxpos : (0 : ℝ) < x := by linarith
  set j : ℕ := ⌈x⌉₊ with hjdef
  have hj1 : 1 ≤ j := Nat.one_le_ceil_iff.2 hxpos
  have hjx : x ≤ (j : ℝ) := Nat.le_ceil x
  have hjx2 : (j : ℝ) ≤ 2 * x := by
    have h := Nat.ceil_lt_add_one (le_of_lt hxpos)
    have : (j : ℝ) < x + 1 := h
    linarith
  set P : ℝ := (n : ℝ) ^ ((4 - (d : ℝ)) / (2 * d)) with hP
  have hPpos : 0 < P := Real.rpow_pos_of_pos hnpos _
  -- the two rpow identities
  have hxsq : x ^ 2 = (n : ℝ) ^ ((2 : ℝ) / d) := by
    rw [hxdef, ← Real.rpow_natCast ((n : ℝ) ^ ((1 : ℝ) / d)) 2, ← Real.rpow_mul hnpos.le]
    congr 1
    push_cast
    ring
  have hxtail : x ^ ((4 - (d : ℝ)) / 2) = P := by
    rw [hxdef, ← Real.rpow_mul hnpos.le, hP]
    congr 1
    field_simp
  have hsplit : (n : ℝ) ^ ((2 : ℝ) / d) * ((n : ℝ) ^ ((1 : ℝ) / 6)
      * (n : ℝ) ^ (-(2 : ℝ) / 3)) = P := by
    rw [← Real.rpow_add hnpos, ← Real.rpow_add hnpos, hP]
    congr 1
    field_simp
    ring
  -- the three terms at the horizon `j`
  have hstep := integral_centeredValue_sq_le hGH hd v hj1 n hpos hsq2 (hintD n)
  rw [← meanOdometer_eq d ν hd1 n] at hstep
  have htailj : (j : ℝ) ^ ((4 - (d : ℝ)) / 2) ≤ P := by
    rw [← hxtail]
    exact Real.rpow_le_rpow_of_nonpos hxpos hjx (by linarith)
  have hjsq : (j : ℝ) ^ 2 ≤ 4 * (n : ℝ) ^ ((2 : ℝ) / d) := by
    rw [← hxsq]
    nlinarith [hjx2, hxpos, Nat.cast_nonneg (α := ℝ) j]
  have hEDnn : 0 ≤ ∫ ζ, sceneryDeviation d ζ n ^ 2 ∂μ :=
    integral_nonneg fun _ => sq_nonneg _
  have hone6 : (1 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 6) := Real.one_le_rpow hnR (by norm_num)
  have hpow23 : (0 : ℝ) ≤ (n : ℝ) ^ (-(2 : ℝ) / 3) := Real.rpow_nonneg hnpos.le _
  have hpow2d : (0 : ℝ) ≤ (n : ℝ) ^ ((2 : ℝ) / d) := Real.rpow_nonneg hnpos.le _
  have hcnn : 0 ≤ meanOdometer (centeredMassLaw d ν) n := by
    unfold Sandpile.meanOdometer
    exact integral_nonneg fun _ => Sandpile.odometer_nonneg _ _ _
  have hED : (∫ ζ, sceneryDeviation d ζ n ^ 2 ∂μ)
      ≤ (4 * K + M') * ((n : ℝ) ^ ((1 : ℝ) / 6) * (n : ℝ) ^ (-(2 : ℝ) / 3)) := by
    have h1 := hM n hn1
    have hclog : meanOdometer (centeredMassLaw d ν) n ≤ K * Real.sqrt (Real.log n) := hKn n hn
    have hsl : Real.sqrt (Real.log n) ≤ 2 * (n : ℝ) ^ ((1 : ℝ) / 6) :=
      sqrt_log_le_rpow_sixth _ hnR
    have hMM : M ≤ M' := by
      have : M ≤ |M| := le_abs_self M
      rw [hM']; linarith
    have h2 : 2 * meanOdometer (centeredMassLaw d ν) n + M
        ≤ (4 * K + M') * (n : ℝ) ^ ((1 : ℝ) / 6) := by
      nlinarith [hK.le, hM'pos.le, hclog, hsl, hMM, hone6]
    calc (∫ ζ, sceneryDeviation d ζ n ^ 2 ∂μ)
        ≤ (2 * meanOdometer (centeredMassLaw d ν) n + M) * (n : ℝ) ^ (-(2 : ℝ) / 3) := h1
      _ ≤ ((4 * K + M') * (n : ℝ) ^ ((1 : ℝ) / 6)) * (n : ℝ) ^ (-(2 : ℝ) / 3) :=
          mul_le_mul_of_nonneg_right h2 hpow23
      _ = (4 * K + M') * ((n : ℝ) ^ ((1 : ℝ) / 6) * (n : ℝ) ^ (-(2 : ℝ) / 3)) := by ring
  have hKM : 0 < 4 * K + M' := by linarith
  have hterm1 : (j : ℝ) ^ 2 * (∫ ζ, sceneryDeviation d ζ n ^ 2 ∂μ)
      ≤ 4 * (4 * K + M') * P := by
    have e1 : (j : ℝ) ^ 2 * (∫ ζ, sceneryDeviation d ζ n ^ 2 ∂μ)
        ≤ (4 * (n : ℝ) ^ ((2 : ℝ) / d)) * (∫ ζ, sceneryDeviation d ζ n ^ 2 ∂μ) :=
      mul_le_mul_of_nonneg_right hjsq hEDnn
    have e2 : (4 * (n : ℝ) ^ ((2 : ℝ) / d)) * (∫ ζ, sceneryDeviation d ζ n ^ 2 ∂μ)
        ≤ (4 * (n : ℝ) ^ ((2 : ℝ) / d))
          * ((4 * K + M') * ((n : ℝ) ^ ((1 : ℝ) / 6) * (n : ℝ) ^ (-(2 : ℝ) / 3))) :=
      mul_le_mul_of_nonneg_left hED (by positivity)
    have e3 : (4 * (n : ℝ) ^ ((2 : ℝ) / d))
          * ((4 * K + M') * ((n : ℝ) ^ ((1 : ℝ) / 6) * (n : ℝ) ^ (-(2 : ℝ) / 3)))
        = 4 * (4 * K + M') * P := by
      rw [← hsplit]; ring
    linarith
  have hBb' := hBb j hj1
  rw [← hν] at hBb'
  have hterm2 : (∫ ζ, ((avg^[j] (fun x => infiniteGreenField ζ x)) 0) ^ 2 ∂μ) ≤ CB * P :=
    hBb'.trans (mul_le_mul_of_nonneg_left htailj hCB.le)
  have hCeq : (∫ ζ, ((avg^[j] (fun y => odometerOf ζ n y)) 0
        - ∫ η, (avg^[j] (fun y => odometerOf η n y)) 0 ∂μ) ^ 2 ∂μ)
      = ∫ ζ, |(avg^[j] (fun y => odometerOf ζ n y)) 0
          - ∫ η, (avg^[j] (fun y => odometerOf η n y)) 0 ∂μ| ^ (2 : ℝ) ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
    show ((avg^[j] (fun y => odometerOf ζ n y)) 0
        - ∫ η, (avg^[j] (fun y => odometerOf η n y)) 0 ∂μ) ^ 2
      = |(avg^[j] (fun y => odometerOf ζ n y)) 0
          - ∫ η, (avg^[j] (fun y => odometerOf η n y)) 0 ∂μ| ^ (2 : ℝ)
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  have hterm3 : (∫ ζ, ((avg^[j] (fun y => odometerOf ζ n y)) 0
        - ∫ η, (avg^[j] (fun y => odometerOf η n y)) 0 ∂μ) ^ 2 ∂μ) ≤ CC' * P := by
    rw [hCeq]
    exact (hCb n j hj1).trans (mul_le_mul_of_nonneg_left htailj hCC'nonneg)
  refine hstep.trans ?_
  linarith [hterm1, hterm2, hterm3, hPpos]

end Sandpile
