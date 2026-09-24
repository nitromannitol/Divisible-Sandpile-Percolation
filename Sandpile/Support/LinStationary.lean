/-
Translation invariance of the threshold events, `sandpile.tex:5453-5454`:

  "In either case, the pair $(J,(u_m)_{m\geq0})$ has a translation-invariant
   law."

Step 2 of `lem:dgt4-path-survival` uses it at `sandpile.tex:5532-5550` to replace
the contact event at the site `X_r` visited at time `r` by the contact event at
the origin, which is what the hypothesis `eq:dgt4-uniform-contact-thresholds`
controls.

The shift `σ ↦ σ(· + y)` preserves the i.i.d. mass law and carries the odometer
and the scenery at `y` to the odometer and the scenery at the origin, so any
event written in those two carries over.  In the independent branch of
`IsThresholdField` the threshold field is a function of the scenery at the site,
so the threshold events translate as well; that is the case proved here.
-/
import Sandpile.Support.Translation
import Sandpile.Support.LinFactor

open MeasureTheory

namespace Sandpile

variable {d : ℕ}

/-- The odometer at a site is a measurable function of the mass field. -/
theorem measurable_odometer (t : ℕ) (x : Site d) :
    Measurable fun σ : Site d → ℝ => odometer σ t x := by
  induction t generalizing x with
  | zero => exact measurable_const
  | succ n ih =>
      have hnb : Measurable fun σ : Site d → ℝ => nbrSum (odometer σ n) x := by
        show Measurable fun σ : Site d → ℝ =>
          ∑ i : Fin d, (odometer σ n (x + unit i) + odometer σ n (x - unit i))
        exact Finset.measurable_sum _ fun i _ => (ih _).add (ih _)
      show Measurable fun σ : Site d → ℝ => relax σ (odometer σ n) x
      show Measurable fun σ : Site d → ℝ =>
        max 0 ((σ x - 1 + nbrSum (odometer σ n) x) / (2 * (d : ℝ)))
      exact measurable_const.max
        ((((measurable_pi_apply x).sub measurable_const).add hnb).div_const _)

/-- The centred mass law is invariant under the shift of the field. -/
theorem centeredMassLaw_preimage_shiftField (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (y : Site d) (S : Set (Site d → ℝ)) (hS : MeasurableSet S) :
    (centeredMassLaw d ν) (shiftField y ⁻¹' S) = (centeredMassLaw d ν) S := by
  set μ : Measure ℝ := ν.map fun z => 1 + 2 * (d : ℝ) * z with hμ
  haveI : IsProbabilityMeasure μ := by
    rw [hμ]; exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hcm : centeredMassLaw d ν = massLaw d μ := by rw [centeredMassLaw, hμ]
  rw [hcm, ← Measure.map_apply (measurable_shiftField y) hS, massLaw_map_shiftField d μ y]

/-- **The threshold events translate, in the independent branch.**  With
`J(x) = -G(0,0)ζ(x)`, the symmetric difference of the contact event and the
threshold event at a site has the same probability as at the origin. -/
theorem measure_threshold_symmDiff_shift (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (J : (Site d → ℝ) → Site d → ℝ)
    (hJ : ∀ σ x, J σ x = -(green d 0 0 * scenery d σ x))
    (m : ℕ) (b : ℝ) (y : Site d) :
    (centeredMassLaw d ν)
        (symmDiff {σ : Site d → ℝ | odometer σ m y = 0} {σ : Site d → ℝ | b < J σ y})
      = (centeredMassLaw d ν)
        (symmDiff {σ : Site d → ℝ | odometer σ m 0 = 0} {σ : Site d → ℝ | b < J σ 0}) := by
  classical
  have hodo : shiftField y ⁻¹' {σ : Site d → ℝ | odometer σ m 0 = 0}
      = {σ : Site d → ℝ | odometer σ m y = 0} := by
    ext σ
    simp only [Set.mem_preimage, Set.mem_setOf_eq, odometer_shiftField σ y m 0, zero_add]
  have hthr : shiftField y ⁻¹' {σ : Site d → ℝ | b < J σ 0}
      = {σ : Site d → ℝ | b < J σ y} := by
    ext σ
    simp only [Set.mem_preimage, Set.mem_setOf_eq, hJ]
    constructor
    · intro h
      simpa [shiftField, scenery, zero_add] using h
    · intro h
      simpa [shiftField, scenery, zero_add] using h
  have hmeas0 : MeasurableSet {σ : Site d → ℝ | odometer σ m 0 = 0} :=
    (measurable_odometer (d := d) m 0) (measurableSet_singleton (0 : ℝ))
  have hmeasJ : MeasurableSet {σ : Site d → ℝ | b < J σ 0} := by
    have hfun : Measurable fun σ : Site d → ℝ => J σ 0 := by
      have : (fun σ : Site d → ℝ => J σ 0)
          = fun σ : Site d → ℝ => -(green d 0 0 * ((σ 0 - 1) / (2 * (d : ℝ)))) := by
        funext σ
        rw [hJ σ 0, scenery]
      rw [this]
      fun_prop
    exact measurableSet_lt measurable_const hfun
  have hpre : shiftField y ⁻¹'
      (symmDiff {σ : Site d → ℝ | odometer σ m 0 = 0} {σ : Site d → ℝ | b < J σ 0})
      = symmDiff {σ : Site d → ℝ | odometer σ m y = 0} {σ : Site d → ℝ | b < J σ y} := by
    rw [Set.preimage_symmDiff, hodo, hthr]
  rw [← hpre]
  exact centeredMassLaw_preimage_shiftField ν y _ ((hmeas0.diff hmeasJ).union (hmeasJ.diff hmeas0))

end Sandpile
