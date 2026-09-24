/-
The stationarity input of Step 2 of case (a) (`sandpile.tex:5104-5107`): the mean of
`|V_\infty-u_m+c|` does not depend on the site.

Translating the scenery by `y` is measure preserving, and it carries the odometer at the
origin to the odometer at `y` (`Support/Stationary.lean`).  The Green field is carried the
same way, but only almost surely: the box exhaustion of `eq:dgt4-infinite-green-field` is
centred at the origin, so the translated field is the limit along a translated exhaustion
and the two limits agree on the almost sure agreement set of `Support/LinGaussShift.lean`.
-/
import Sandpile.Support.LinGaussShift
import Sandpile.Support.Dgt4AValueMemLp

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}

/-- **Translation equivariance of the Gaussian Green field, in the i.i.d. normalization.**
Shifting the scenery by `y` moves the field at the origin to the field at `y`. -/
theorem ae_infiniteGreenField_iid_shift (hd : 5 ≤ d) (v : ℝ≥0) (y : Site d) :
    ∀ᵐ ζ ∂(LatticeProb.iidLaw d (gaussianReal 0 v)),
      infiniteGreenField (shiftField y ζ) 0 = infiniteGreenField ζ y := by
  have hms := measurableSet_greenShiftAgree (d := d) y
  have hg := ae_mem_greenShiftAgree_gauss hd (Real.sqrt (v : ℝ)) y
    (fun n omg => infiniteGreenFieldPartial_shift_eq n (Real.sqrt (v : ℝ)) omg y)
  have hiid := ae_of_ae_gauss v _ hms hg
  filter_upwards [hiid] with zeta hzeta
  exact infiniteGreenField_shift_of_mem y zeta hzeta.1 hzeta.2

/-- **The mean of `|V_\infty-u_t+c|` does not depend on the site.**  This is the
"stationarity" of `sandpile.tex:5099-5102`. -/
theorem integral_abs_centeredValue_site_eq (hd : 5 ≤ d) (v : ℝ≥0) (t : ℕ) (c : ℝ)
    (y : Site d) :
    (∫ ζ, |infiniteGreenField ζ y - odometerOf ζ t y + c|
        ∂(LatticeProb.iidLaw d (gaussianReal 0 v)))
      = ∫ ζ, |infiniteGreenField ζ 0 - odometerOf ζ t 0 + c|
        ∂(LatticeProb.iidLaw d (gaussianReal 0 v)) := by
  have hmeas : AEStronglyMeasurable
      (fun ζ : Site d → ℝ => |infiniteGreenField ζ 0 - odometerOf ζ t 0 + c|)
      ((massLaw d (gaussianReal 0 v)).map (shiftField y)) := by
    rw [massLaw_map_shiftField]
    exact (((aemeasurable_infiniteGreenField_iid hd v 0).sub
        (measurable_odometerOf t 0).aemeasurable).add_const c).abs.aestronglyMeasurable
  have h1 : ∫ ζ, |infiniteGreenField (shiftField y ζ) 0 - odometerOf (shiftField y ζ) t 0 + c|
        ∂(massLaw d (gaussianReal 0 v))
      = ∫ ζ, |infiniteGreenField ζ 0 - odometerOf ζ t 0 + c| ∂(massLaw d (gaussianReal 0 v)) := by
    rw [← integral_map (measurable_shiftField y).aemeasurable hmeas, massLaw_map_shiftField]
  rw [show LatticeProb.iidLaw d (gaussianReal 0 v) = massLaw d (gaussianReal 0 v) from rfl, ← h1]
  have hae : ∀ᵐ ζ ∂(massLaw d (gaussianReal 0 v)),
      infiniteGreenField (shiftField y ζ) 0 = infiniteGreenField ζ y :=
    ae_infiniteGreenField_iid_shift hd v y
  refine integral_congr_ae ?_
  filter_upwards [hae] with ζ hζ
  show |infiniteGreenField ζ y - odometerOf ζ t y + c|
      = |infiniteGreenField (shiftField y ζ) 0 - odometerOf (shiftField y ζ) t 0 + c|
  rw [hζ, odometerOf_shiftField ζ y t 0, zero_add]

/-- The Gaussian Green field at any site is square integrable. -/
theorem memLp_two_infiniteGreenField_site (hd : 5 ≤ d) (v : ℝ≥0) (y : Site d) :
    MemLp (fun ζ : Site d → ℝ => infiniteGreenField ζ y) 2
      (LatticeProb.iidLaw d (gaussianReal 0 v)) := by
  have hS : Measurable fun (ω : Site d → ℝ) (z : Site d) => Real.sqrt (v : ℝ) * ω z := by
    fun_prop
  have hAE : AEStronglyMeasurable (fun ζ : Site d → ℝ => infiniteGreenField ζ y)
      (LatticeProb.iidLaw d (gaussianReal 0 v)) :=
    (aemeasurable_infiniteGreenField_iid hd v y).aestronglyMeasurable
  rw [iidLaw_gaussianReal_eq_map d v] at hAE ⊢
  rw [memLp_map_measure_iff hAE hS.aemeasurable]
  have hiso : MemLp (fun ω : Site d → ℝ =>
      Real.sqrt (v : ℝ) * ⇑(LatticeProb.gaussIso (greenLp d hd y)) ω) 2
      (LatticeProb.gaussLaw (Site d)) :=
    (Lp.memLp (LatticeProb.gaussIso (greenLp d hd y))).const_mul (Real.sqrt (v : ℝ))
  refine hiso.ae_eq ?_
  filter_upwards [ae_infiniteGreenField_eq hd y (Real.sqrt (v : ℝ))] with ω hω
  rw [Function.comp_apply, hω]

/-- The centred value at any site is square integrable. -/
theorem memLp_two_centeredValue_site (hd : 5 ≤ d) (v : ℝ≥0)
    (hsq : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 v)) (t : ℕ) (c : ℝ) (y : Site d) :
    MemLp (fun ζ : Site d → ℝ => infiniteGreenField ζ y - odometerOf ζ t y + c) 2
      (LatticeProb.iidLaw d (gaussianReal 0 v)) :=
  ((memLp_two_infiniteGreenField_site hd v y).sub
      (memLp_two_odometerOf (gaussianReal 0 v) hsq t y)).add (memLp_const c)

/-- **`P^k` does not change the mean of `|V_\infty-u_t+c|`.**  The heat kernel is a
probability and the mean does not depend on the site. -/
theorem integral_avgIterate_abs_centeredValue_eq (hd : 5 ≤ d) (v : ℝ≥0)
    (hsq : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 v)) (t : ℕ) (c : ℝ) (k : ℕ) :
    (∫ ζ, (avg^[k] (fun x => |infiniteGreenField ζ x - odometerOf ζ t x + c|)) 0
        ∂(LatticeProb.iidLaw d (gaussianReal 0 v)))
      = ∫ ζ, |infiniteGreenField ζ 0 - odometerOf ζ t 0 + c|
        ∂(LatticeProb.iidLaw d (gaussianReal 0 v)) :=
  integral_avgIterate_eq_of_site_invariant (by omega) (gaussianReal 0 v)
    (fun ζ y => |infiniteGreenField ζ y - odometerOf ζ t y + c|)
    (fun y => ((memLp_two_centeredValue_site hd v hsq t c y).abs).integrable (by norm_num))
    (fun y => integral_abs_centeredValue_site_eq hd v t c y) k

end Sandpile
