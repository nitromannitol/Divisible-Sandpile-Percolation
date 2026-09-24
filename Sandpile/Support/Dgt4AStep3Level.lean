/-
**The conditioning level of Steps 3 and 4 of case (a)** (`sandpile.tex:5133-5140`):
`-V_\infty(0)=\E u_n(0)+\Sigma^2y/\E u_n(0)`.

In the splitting of `Support/Dgt4ACondition.lean` the conditioned value is
`V_\infty(0)=\sqrt v\,s\,\|G(0,\cdot)\|`, so the paper's level `y` is the level
`s=-(\E u_n(0)+\Sigma^2y/\E u_n(0))/\Sigma` of that splitting, which is `condLevel` below.
At that level the field at the origin is deterministic, which is
`ae_infiniteGreenField_condLevel`, and the exceptional set of
`eq:dgt4-gaussian-positive-off-origin` is `condBad`, whose probability tends to zero by the
union bound of `Support/Dgt4ACondTail.lean` and the arithmetic of
`Support/Dgt4AStep3Good.lean`.
-/
import Sandpile.Support.Dgt4AStep3Good
import Sandpile.Support.Dgt4AConditionVar
import Sandpile.Support.Dgt4ACorrGap

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}

/-- The mean odometer of the Gaussian scenery tends to infinity, at the rate of
`eq:dgt4-gaussian-height-order`. -/
theorem tendsto_meanOdometer_gaussian_atTop (hGH : Sandpile.External.GreenBoundsHigh)
    (hd : 5 ≤ d) (v : ℝ≥0) (hv : v ≠ 0) :
    Tendsto (fun n : ℕ => meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n) atTop atTop := by
  obtain ⟨c₀, hc₀, hlow⟩ := exists_sqrt_log_le_meanOdometer hGH hd v hv
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  exact tendsto_atTop_mono' atTop hlow (Filter.Tendsto.const_mul_atTop hc₀ hsqrt)

/-- The conditioning level of `sandpile.tex:5128`: the value of the splitting coordinate `s`
at which `-V_\infty(0)=\E u_n(0)+\Sigma^2y/\E u_n(0)`. -/
noncomputable def condLevel (d : ℕ) (hd : 5 ≤ d) (v : ℝ≥0) (y : ℝ) (n : ℕ) : ℝ :=
  -(meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n
      + (fieldVar d v : ℝ) * y / meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n)
    / (Real.sqrt (v : ℝ) * ‖greenLp d hd (0 : Site d)‖)

theorem condLevel_mul (hd : 5 ≤ d) {v : ℝ≥0} (hv : v ≠ 0) (y : ℝ) (n : ℕ) :
    Real.sqrt (v : ℝ) * condLevel d hd v y n * ‖greenLp d hd (0 : Site d)‖
      = -(meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n
        + (fieldVar d v : ℝ) * y
          / meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n) := by
  have hvpos : (0 : ℝ) < Real.sqrt (v : ℝ) := Real.sqrt_pos.2 (coe_pos_of_ne_zero hv)
  have hN : (0 : ℝ) < ‖greenLp d hd (0 : Site d)‖ := norm_greenLp_pos hd
  rw [condLevel]
  field_simp

/-- **At the conditioning level the field at the origin is deterministic**
(`sandpile.tex:5104`, `sandpile.tex:5128`). -/
theorem ae_infiniteGreenField_condLevel (hd : 5 ≤ d) {v : ℝ≥0} (hv : v ≠ 0) (y : ℝ) (n : ℕ) :
    ∀ᵐ r ∂((LatticeProb.gaussLaw (Site d)).map (residField d hd)),
      infiniteGreenField (condScenery d hd (Real.sqrt (v : ℝ)) r (condLevel d hd v y n)) 0
        = -(meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n
          + (fieldVar d v : ℝ) * y
            / meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n) := by
  filter_upwards [ae_tendsto_greenPartialSum_resid hd] with r hr
  rw [condScenery_eq, infiniteGreenField_shift_eq hd _ hr, condLevel_mul hd hv]

/-- The exceptional set of `eq:dgt4-gaussian-positive-off-origin` (`sandpile.tex:5179-5192`):
the residuals at which the conditioned field fails to be positive somewhere on the punctured
box of radius `k_n+1`. -/
def condBad (d : ℕ) (hd : 5 ≤ d) (v : ℝ≥0) (y : ℝ) (n : ℕ) : Set (Site d → ℝ) :=
  {r | ∃ z ∈ (boxFinset (0 : Site d) (dgt4Horizon d n + 1)).erase 0,
    infiniteGreenField (condScenery d hd (Real.sqrt (v : ℝ)) r (condLevel d hd v y n)) z
      + meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n ≤ 0}

/-- Off the exceptional set the payoff of the stopping comparison is nonnegative on the
punctured box, which is the hypothesis of `abs_condReflected_sub_le`. -/
theorem good_of_notMem_condBad (hd : 5 ≤ d) (v : ℝ≥0) (y : ℝ) (n : ℕ)
    {r : Site d → ℝ} (hr : r ∉ condBad d hd v y n) :
    ∀ z : Site d, z ≠ 0 → boxDist z 0 ≤ dgt4Horizon d n + 1 →
      0 ≤ infiniteGreenField (condScenery d hd (Real.sqrt (v : ℝ)) r (condLevel d hd v y n)) z
        + meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n := by
  intro z hz hbox
  by_contra hneg
  exact hr ⟨z, Finset.mem_erase.2 ⟨hz, mem_boxFinset_iff.2 (by rwa [boxDist_comm])⟩,
    le_of_not_ge hneg⟩

/-- **`eq:dgt4-gaussian-positive-off-origin`** (`sandpile.tex:5179-5192`): the exceptional set
of Step 3 has vanishing conditional probability. -/
theorem tendsto_measure_condBad (hGH : Sandpile.External.GreenBoundsHigh)
    (hd : 5 ≤ d) (v : ℝ≥0) (hv : v ≠ 0) {K y : ℝ} (hy : |y| ≤ K) :
    Tendsto (fun n : ℕ => (((LatticeProb.gaussLaw (Site d)).map (residField d hd))
        (condBad d hd v y n)).toReal) atTop (𝓝 0) := by
  obtain ⟨rho, hrho0, hrho1, hgap⟩ := exists_correlation_gap hd
  have hcc : (0 : ℝ) < Real.sqrt (v : ℝ) := Real.sqrt_pos.2 (coe_pos_of_ne_zero hv)
  have hN : (0 : ℝ) < ‖greenLp d hd (0 : Site d)‖ := norm_greenLp_pos hd
  set b : ℝ := ((1 - rho) / 2 / Real.sqrt (v : ℝ)) ^ 2
    / (2 * ‖greenLp d hd (0 : Site d)‖ ^ 2) with hbdef
  have hb : 0 < b := by
    rw [hbdef]
    have h1 : (0 : ℝ) < (1 - rho) / 2 / Real.sqrt (v : ℝ) := by
      apply div_pos (by linarith) hcc
    positivity
  have hK : (0 : ℝ) ≤ K := le_trans (abs_nonneg y) hy
  have hS : (0 : ℝ) ≤ ((fieldVar d v : ℝ≥0) : ℝ) := (fieldVar d v).coe_nonneg
  have hatt := tendsto_meanOdometer_gaussian_atTop hGH hd v hv
  have hmaj := tendsto_boxCard_mul_exp_neg_sq hGH hd v hv hb
  refine squeeze_zero' (Filter.Eventually.of_forall fun n => ENNReal.toReal_nonneg) ?_ hmaj
  have hlin : Tendsto
      (fun n : ℕ => meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n * (1 - rho))
      atTop atTop :=
    hatt.atTop_mul_const (by linarith : (0 : ℝ) < 1 - rho)
  filter_upwards [hatt.eventually_gt_atTop 0, hatt.eventually_ge_atTop 1,
    hlin.eventually_ge_atTop (2 * (K * ((fieldVar d v : ℝ≥0) : ℝ) * rho))] with n ha ha1 hl
  have hlarge : 2 * (K * ((fieldVar d v : ℝ≥0) : ℝ) * rho)
      ≤ (meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n) ^ 2 * (1 - rho) := by
    have hstep : meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n
        ≤ (meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n) ^ 2 := by nlinarith [ha1]
    nlinarith [hl, mul_nonneg (sub_nonneg.2 hstep) (by linarith : (0:ℝ) ≤ 1 - rho)]
  have hub := measure_resid_exists_nonpos_le hd hcc (rho := rho)
    (a := meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n) (K := K)
    (S := ((fieldVar d v : ℝ≥0) : ℝ)) (y := y) (s := condLevel d hd v y n)
    (dgt4Horizon d n + 1) hgap ha hS hy hrho1 hlarge (condLevel_mul hd hv y n)
  have hexp : -((meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n * (1 - rho) / 2
        / Real.sqrt (v : ℝ)) ^ 2 / (2 * ‖greenLp d hd (0 : Site d)‖ ^ 2))
      = -(b * (meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n) ^ 2) := by
    rw [hbdef]
    field_simp
  rw [hexp] at hub
  have hfin : ((((boxFinset (0 : Site d) (dgt4Horizon d n + 1)).erase 0).card : ℝ≥0∞) *
      ENNReal.ofReal (2 * Real.exp
        (-(b * (meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n) ^ 2)))) ≠ ⊤ := by
    finiteness
  have h1 := ENNReal.toReal_mono hfin hub
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h1
  simp only [ENNReal.toReal_natCast] at h1
  have hcards : ((((boxFinset (0 : Site d) (dgt4Horizon d n + 1)).erase 0).card : ℝ))
      ≤ ((boxFinset (0 : Site d) (dgt4Horizon d n + 1)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.erase_subset _ _)
  have hpos : (0 : ℝ) ≤ 2 * Real.exp
      (-(b * (meanOdometer (centeredMassLaw d (gaussianReal 0 v)) n) ^ 2)) := by positivity
  exact le_trans h1 (mul_le_mul_of_nonneg_right hcards hpos)

end Sandpile
