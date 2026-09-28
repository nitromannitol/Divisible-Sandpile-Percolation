import Sandpile.Support.Dgt4AStep4Neg
import Sandpile.Support.Dgt4ASceneryFirstMoment

/-!
**The integral representation of Step 4 of case (a)**
(`eq:dgt4-gaussian-integral-representation`, `sandpile.tex:5258-5266`):

  `\frac{\E u_n(0)}{\Sigma^2\P(-V_\infty(0)>\E u_n(0))}\E(-\zeta(0)-Pu_n(0))_+
     =\int_\R m_n(y)\rho_n(y)\,dy` .

Three identities compose to it.  The mean increment is the mean of the reflection term
(`lem:reflection-increment`); the reflection term is averaged over the conditioning level by
`integral_iidLaw_gauss_shift`; and the standard Gaussian level `s` is turned into the paper's
variable `y` by the affine substitution `s=-(\E u_n(0)+\Sigma^2y/\E u_n(0))/\Sigma` of
`Support/Dgt4AStep4Rep.lean`, under which the standard Gaussian density becomes
`\Sigma\varphi_{0,\Sigma^2}(\E u_n(0)+\Sigma^2y/\E u_n(0))` and the Jacobian is
`\Sigma/\E u_n(0)`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}

/-- The mean of the reflection term is the increment of the mean odometer
(`eq:reflection-increment`, `sandpile.tex:899-905`), in the scenery normalization. -/
theorem integral_reflectionTerm_eq_increment (hd : 1 ≤ d) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hint : Integrable id ν) (hmean : ∫ w, w ∂ν = 0)
    (hpos : Integrable (fun z : ℝ => max z 0) ν) (n : ℕ) :
    (∫ ζ : Site d → ℝ, reflectionTerm ζ n 0 ∂(LatticeProb.iidLaw d ν))
      = meanOdometer (centeredMassLaw d ν) (n + 1) - meanOdometer (centeredMassLaw d ν) n := by
  have hIincr : Integrable (fun ζ : Site d → ℝ =>
      odometerOf ζ (n + 1) 0 - odometerOf ζ n 0) (LatticeProb.iidLaw d ν) :=
    (integrable_odometerOf d ν hpos (n + 1) 0).sub (integrable_odometerOf d ν hpos n 0)
  have hIrefl : Integrable (fun ζ : Site d → ℝ => reflectionTerm ζ n 0)
      (LatticeProb.iidLaw d ν) := integrable_reflectionTerm ν hint hpos n 0
  have hfun : (fun ζ : Site d → ℝ => sceneryDeviation d ζ n)
      = fun ζ => (odometerOf ζ (n + 1) 0 - odometerOf ζ n 0) - reflectionTerm ζ n 0 :=
    funext fun ζ => sceneryDeviation_eq_increment_sub ζ n
  have hzero := integral_sceneryDeviation_eq_zero (d := d) hd ν hint hmean hpos n
  rw [hfun, integral_sub hIincr hIrefl, integral_odometerOf_increment (d := d) hd ν hpos n]
    at hzero
  linarith

/-- `\Sigma^2=v\sum_zG(0,z)^2` (`sandpile.tex:4967`). -/
theorem coe_fieldVar (hd : 5 ≤ d) (v : ℝ≥0) :
    ((fieldVar d v : ℝ≥0) : ℝ) = (v : ℝ) * greenSqSum d := by
  have h1 : (1 : ℝ) ≤ greenSqSum d := one_le_greenSqSum hd
  refine Real.coe_toNNReal _ ?_
  have := v.coe_nonneg
  nlinarith

/-- `\Sigma=\sqrt v\,\|G(0,\cdot)\|_2`. -/
theorem sqrt_fieldVar (hd : 5 ≤ d) (v : ℝ≥0) :
    Real.sqrt ((fieldVar d v : ℝ≥0) : ℝ)
      = Real.sqrt (v : ℝ) * ‖greenLp d hd (0 : Site d)‖ := by
  rw [coe_fieldVar hd v, Real.sqrt_mul v.coe_nonneg, ← norm_greenLp_sq hd,
    Real.sqrt_sq (norm_nonneg _)]

/-- The standard Gaussian density at `x/\Sigma` is `\Sigma` times the density of variance
`\Sigma^2` at `x`. -/
theorem gaussianPDFReal_div_sqrt (w : ℝ≥0) (hw : w ≠ 0) (x : ℝ) :
    gaussianPDFReal 0 1 (x / Real.sqrt ((w : ℝ)))
      = Real.sqrt ((w : ℝ)) * gaussianPDFReal 0 w x := by
  have hwpos : (0 : ℝ) < (w : ℝ) := coe_pos_of_ne_zero hw
  have hsw : (0 : ℝ) < Real.sqrt (w : ℝ) := Real.sqrt_pos.2 hwpos
  have hsq : Real.sqrt (w : ℝ) ^ 2 = (w : ℝ) := Real.sq_sqrt hwpos.le
  have hexp : -(x / Real.sqrt (w : ℝ) - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ))
      = -(x - 0) ^ 2 / (2 * (w : ℝ)) := by
    rw [NNReal.coe_one]
    field_simp
    nlinarith [hsq]
  have hnorm : (Real.sqrt (2 * Real.pi * ((1 : ℝ≥0) : ℝ)))⁻¹
      = Real.sqrt (w : ℝ) * (Real.sqrt (2 * Real.pi * ((w : ℝ))))⁻¹ := by
    rw [NNReal.coe_one, mul_one,
      show (2 : ℝ) * Real.pi * (w : ℝ) = (w : ℝ) * (2 * Real.pi) by ring,
      Real.sqrt_mul hwpos.le]
    field_simp
  rw [gaussianPDFReal, gaussianPDFReal, hexp, hnorm]
  ring

/-- The conditional mean `m_n(y)` of `sandpile.tex:5254-5256`: the scaled conditional mean of
the positive part of the reflected increment at the level `y`. -/
noncomputable def condMeanReflected (d : ℕ) (hd : 5 ≤ d) (v : ℝ≥0) (n : ℕ) (y : ℝ) : ℝ :=
  ∫ r, max (meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n
      / ((fieldVar d v : ℝ≥0) : ℝ)
      * condReflected d hd (Real.sqrt (v : ℝ)) (condLevel d hd v y n) n r) 0
    ∂((LatticeProb.gaussLaw (Site d)).map (residField d hd))

/-- The normalized density `\rho_n(y)` of `eq:dgt4-gaussian-density-ratio`
(`sandpile.tex:5245-5251`). -/
noncomputable def levelDensity (w : ℝ≥0) (t y : ℝ) : ℝ :=
  (w : ℝ) / t * gaussianPDFReal 0 w (t + (w : ℝ) * y / t) / gaussianUpperTail w t

/-- **The conditioning on the level `y`** (`eq:dgt4-gaussian-integral-representation`,
`sandpile.tex:5257-5261`): the mean of any integrable functional of the scenery is the
average of its conditional means against the density of the level. -/
theorem integral_iidLaw_eq_level_integral (hd : 5 ≤ d) (v : ℝ≥0) (hv : v ≠ 0) (n : ℕ)
    (ha : 0 < meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n)
    (F : (Site d → ℝ) → ℝ) (hF : Integrable F (LatticeProb.iidLaw d (gaussianReal 0 v))) :
    (∫ ζ, F ζ ∂(LatticeProb.iidLaw d (gaussianReal 0 v)))
      = ((fieldVar d v : ℝ≥0) : ℝ)
          / meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n
        * ∫ y : ℝ, gaussianPDFReal 0 (fieldVar d v)
            (meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n
              + ((fieldVar d v : ℝ≥0) : ℝ) * y
                / meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n)
          * (∫ r, F (condScenery d hd (Real.sqrt (v : ℝ)) r (condLevel d hd v y n))
              ∂((LatticeProb.gaussLaw (Site d)).map (residField d hd))) := by
  classical
  set ρ : Measure (Site d → ℝ) :=
    (LatticeProb.gaussLaw (Site d)).map (residField d hd) with hρ
  set S : ℝ := ((fieldVar d v : ℝ≥0) : ℝ) with hSdef
  have hSpos : (0 : ℝ) < S := coe_pos_of_ne_zero (fieldVar_ne_zero hd hv)
  have hSne : S ≠ 0 := ne_of_gt hSpos
  set cc : ℝ := Real.sqrt (v : ℝ) with hccdef
  have hccpos : (0 : ℝ) < cc := Real.sqrt_pos.2 (coe_pos_of_ne_zero hv)
  set N : ℝ := ‖greenLp d hd (0 : Site d)‖ with hNdef
  have hNpos : (0 : ℝ) < N := norm_greenLp_pos hd
  set A : ℝ := meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n with hAdef
  have hAne : A ≠ 0 := ne_of_gt ha
  have hsig : cc * N = Real.sqrt S := (sqrt_fieldVar hd v).symm
  have hsigpos : (0 : ℝ) < Real.sqrt S := Real.sqrt_pos.2 hSpos
  have hsne : Real.sqrt S ≠ 0 := ne_of_gt hsigpos
  set M : ℝ → ℝ := fun s => ∫ r, F (condScenery d hd cc r s) ∂ρ with hMdef
  have hMval : ∀ s : ℝ, M s = ∫ r, F (condScenery d hd cc r s) ∂ρ := fun _ => rfl
  have hshift := integral_iidLaw_gauss_shift hd v F hF
  have hinner : ∀ s : ℝ, (∫ r, F
      (fun z => Real.sqrt (v : ℝ) * (r z + s * (greenUnit d hd : Site d → ℝ) z)) ∂ρ)
      = M s := fun s => rfl
  rw [funext hinner] at hshift
  set g : ℝ → ℝ := fun s => gaussianPDFReal 0 1 s * M s with hgdef
  have hgval : ∀ s : ℝ, g s = gaussianPDFReal 0 1 s * M s := fun _ => rfl
  have hdens : (∫ s, M s ∂(gaussianReal 0 1)) = ∫ s : ℝ, g s := by
    rw [integral_gaussianReal_eq_integral_smul (one_ne_zero)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only [smul_eq_mul, hgval]
  rw [hdens] at hshift
  set bb : ℝ := -A / (cc * N) with hbb
  set cf : ℝ := -(S / (A * (cc * N))) with hcf
  have hKpos : (0 : ℝ) < S / (A * (cc * N)) := by positivity
  have hlevel : ∀ y : ℝ, bb + cf * y = condLevel d hd v y n := by
    intro y
    rw [hbb, hcf, condLevel, ← hSdef, ← hccdef, ← hNdef, ← hAdef]
    field_simp
    ring
  have habs : |cf| = S / (A * (cc * N)) := by
    rw [hcf, abs_neg, abs_of_pos hKpos]
  have hsub := integral_comp_affine g cf bb
  rw [habs] at hsub
  have hgl : (fun y : ℝ => g (bb + cf * y)) = fun y : ℝ => g (condLevel d hd v y n) :=
    funext fun y => by simp only [hlevel]
  rw [hgl] at hsub
  have hmain : (∫ s : ℝ, g s)
      = (S / (A * (cc * N))) * ∫ y : ℝ, g (condLevel d hd v y n) := by
    rw [hsub, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hKpos), one_mul]
  rw [hmain] at hshift
  have hpdf : ∀ y : ℝ, gaussianPDFReal 0 1 (condLevel d hd v y n)
      = Real.sqrt S * gaussianPDFReal 0 (fieldVar d v) (A + S * y / A) := by
    intro y
    have hval : condLevel d hd v y n = -(A + S * y / A) / Real.sqrt S := by
      rw [condLevel, ← hSdef, ← hccdef, ← hNdef, ← hAdef, hsig]
    rw [hval, gaussianPDFReal_div_sqrt (fieldVar d v) (fieldVar_ne_zero hd hv), ← hSdef]
    congr 1
    rw [gaussianPDFReal, gaussianPDFReal]
    congr 2
    ring
  set J : ℝ := ∫ y : ℝ, gaussianPDFReal 0 (fieldVar d v) (A + S * y / A)
    * M (condLevel d hd v y n) with hJ
  have hgJ : (∫ y : ℝ, g (condLevel d hd v y n)) = Real.sqrt S * J := by
    rw [hJ, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show g (condLevel d hd v y n)
        = Real.sqrt S * (gaussianPDFReal 0 (fieldVar d v) (A + S * y / A)
          * M (condLevel d hd v y n))
    rw [hgval, hpdf y]
    ring
  rw [hgJ] at hshift
  rw [hshift, hsig, hJ]
  field_simp

/-- **The integral representation** (`eq:dgt4-gaussian-integral-representation`,
`sandpile.tex:5257-5261`), before dividing by the threshold probability. -/
theorem integral_condMeanReflected_pdf (hd : 5 ≤ d) (v : ℝ≥0) (hv : v ≠ 0) (n : ℕ)
    (ha : 0 < meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n) :
    (∫ y : ℝ, ((fieldVar d v : ℝ≥0) : ℝ)
          / meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n
        * gaussianPDFReal 0 (fieldVar d v)
            (meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n
              + ((fieldVar d v : ℝ≥0) : ℝ) * y
                / meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n)
        * condMeanReflected d hd v n y)
      = meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n
          / ((fieldVar d v : ℝ≥0) : ℝ)
        * (meanOdometer (centeredMassLaw d (gaussianReal 0 v)) (n + 1)
          - meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n) := by
  have hmem2 : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 v) := by
    simpa using memLp_id_gaussianReal (μ := 0) (v := v) 2
  have hint : Integrable (id : ℝ → ℝ) (gaussianReal 0 v) := hmem2.integrable (by norm_num)
  have hmeanz : (∫ z, z ∂(gaussianReal 0 v)) = 0 := ProbabilityTheory.integral_id_gaussianReal
  have hposint : Integrable (fun z : ℝ => max z 0) (gaussianReal 0 v) := by
    refine hint.mono ((continuous_id.max continuous_const).measurable.aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun z => ?_
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    show |max z 0| ≤ |z|
    rcases le_or_gt 0 z with h | h
    · rw [max_eq_left h]
    · rw [max_eq_right h.le, abs_zero]
      exact abs_nonneg z
  have hrefl : Integrable (fun ζ : Site d → ℝ => reflectionTerm ζ n 0)
      (LatticeProb.iidLaw d (gaussianReal 0 v)) :=
    integrable_reflectionTerm (gaussianReal 0 v) hint hposint n 0
  have hrep := integral_iidLaw_eq_level_integral hd v hv n ha
    (fun ζ => reflectionTerm ζ n 0) hrefl
  rw [integral_reflectionTerm_eq_increment (d := d) (by omega) (gaussianReal 0 v)
    hint hmeanz hposint n] at hrep
  set ρ : Measure (Site d → ℝ) :=
    (LatticeProb.gaussLaw (Site d)).map (residField d hd) with hρ
  set S : ℝ := ((fieldVar d v : ℝ≥0) : ℝ) with hSdef
  have hSpos : (0 : ℝ) < S := coe_pos_of_ne_zero (fieldVar_ne_zero hd hv)
  have hSne : S ≠ 0 := ne_of_gt hSpos
  set cc : ℝ := Real.sqrt (v : ℝ) with hccdef
  set A : ℝ := meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n with hAdef
  have hAne : A ≠ 0 := ne_of_gt ha
  have hinner : ∀ y : ℝ, (∫ r, reflectionTerm
      (condScenery d hd cc r (condLevel d hd v y n)) n 0 ∂ρ)
      = S / A * condMeanReflected d hd v n y := by
    intro y
    rw [condMeanReflected, ← hSdef, ← hAdef, ← hccdef, ← hρ, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
    show max 0 (condReflected d hd cc (condLevel d hd v y n) n r)
        = S / A * max (A / S * condReflected d hd cc (condLevel d hd v y n) n r) 0
    rw [mul_max_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ S / A), mul_zero, max_comm]
    congr 1
    field_simp
  set J : ℝ := ∫ y : ℝ, gaussianPDFReal 0 (fieldVar d v) (A + S * y / A)
    * condMeanReflected d hd v n y with hJ
  have hrw : (∫ y : ℝ, gaussianPDFReal 0 (fieldVar d v) (A + S * y / A)
      * ∫ r, reflectionTerm (condScenery d hd cc r (condLevel d hd v y n)) n 0 ∂ρ)
      = S / A * J := by
    rw [hJ, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hinner]
    ring
  rw [hrw] at hrep
  have hgoal : (∫ y : ℝ, S / A * gaussianPDFReal 0 (fieldVar d v) (A + S * y / A)
      * condMeanReflected d hd v n y) = S / A * J := by
    rw [hJ, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    ring
  rw [hgoal, hrep]
  field_simp


end Sandpile
