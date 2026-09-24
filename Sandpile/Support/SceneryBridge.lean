/-
The bridge between the two languages of the paper: the mass field `σ` with law
`centeredMassLaw d ν`, in which the main theorems are stated, and the scenery
`ζ = (σ - 1)/(2d)` with law `iidLaw d ν`, in which the estimates of
`ssec:expl-d5` are carried out.  The odometer of a mass field is the odometer of
its scenery, the scenery of the mass law is the i.i.d. law of the one-site
scenery, and hence every event and every mean transports.
-/
import Sandpile.Law
import Sandpile.Support.Odometer
import Sandpile.Support.Stationary

open MeasureTheory ProbabilityTheory

namespace Sandpile

variable {d : ℕ}

theorem odometer_eq_odometerOf (σ : Site d → ℝ) (t : ℕ) :
    odometer σ t = odometerOf (scenery d σ) t := by
  induction t with
  | zero => rfl
  | succ n ih =>
      funext x
      show relax σ (odometer σ n) x = max 0 (scenery d σ x + avg (odometerOf (scenery d σ) n) x)
      rw [relax_eq_scenery, ih]

theorem map_scenery_centeredMassLaw (d : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hd : 1 ≤ d) : (centeredMassLaw d ν).map (scenery d) = LatticeProb.iidLaw d ν := by
  have hd0 : (2 * (d : ℝ)) ≠ 0 := by
    have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    positivity
  set g : ℝ → ℝ := fun z => 1 + 2 * (d : ℝ) * z with hg
  set f : ℝ → ℝ := fun z => (z - 1) / (2 * (d : ℝ)) with hf
  have hmg : Measurable g := by fun_prop
  have hmf : Measurable f := by fun_prop
  haveI : IsProbabilityMeasure (ν.map g) := Measure.isProbabilityMeasure_map hmg.aemeasurable
  have hsc : (scenery d : (Site d → ℝ) → Site d → ℝ) = fun σ i => f (σ i) := rfl
  unfold centeredMassLaw massLaw LatticeProb.iidLaw
  rw [hsc, Measure.infinitePi_map_pi _ (f := fun _ : Site d => f) (fun _ => hmf)]
  congr 1
  funext _
  rw [Measure.map_map hmf hmg]
  have : f ∘ g = id := by
    funext z
    show (1 + 2 * (d : ℝ) * z - 1) / (2 * (d : ℝ)) = z
    field_simp
    ring
  rw [this, Measure.map_id]

/-- The scenery is a measurable map of the mass field. -/
theorem measurable_scenery (d : ℕ) : Measurable (scenery (d := d)) := by
  refine measurable_pi_lambda _ fun x => ?_
  exact ((measurable_pi_apply x).sub measurable_const).div_const _

/-- Any event of the scenery has the same probability under the mass law as under
the i.i.d. law of the one-site scenery. -/
theorem centeredMassLaw_scenery_preimage (d : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hd : 1 ≤ d) {A : Set (Site d → ℝ)} (hA : MeasurableSet A) :
    centeredMassLaw d ν (scenery d ⁻¹' A) = LatticeProb.iidLaw d ν A := by
  rw [← map_scenery_centeredMassLaw d ν hd,
    Measure.map_apply (measurable_scenery d) hA]

/-- `E u_t(0)` is the mean of the odometer written in the scenery. -/
theorem meanOdometer_eq (d : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν] (hd : 1 ≤ d)
    (t : ℕ) :
    meanOdometer (centeredMassLaw d ν) t
      = ∫ ζ, odometerOf ζ t 0 ∂(LatticeProb.iidLaw d ν) := by
  have h1 : meanOdometer (centeredMassLaw d ν) t
      = ∫ σ, odometerOf (scenery d σ) t 0 ∂(centeredMassLaw d ν) := by
    rw [meanOdometer]
    exact integral_congr_ae (Filter.Eventually.of_forall fun σ =>
      congrFun (odometer_eq_odometerOf σ t) 0)
  have h2 := integral_map (μ := centeredMassLaw d ν) (φ := scenery d)
      (f := fun ζ : Site d → ℝ => odometerOf ζ t 0)
      (measurable_scenery d).aemeasurable
      (by rw [map_scenery_centeredMassLaw d ν hd]
          exact (measurable_odometerOf t 0).aestronglyMeasurable)
  rw [map_scenery_centeredMassLaw d ν hd] at h2
  rw [h1, ← h2]


open MeasureTheory ProbabilityTheory

/-- The mean odometer of the mass field transports to the mean of the scenery
odometer under the i.i.d. law: `E u_t(0)` is the same number in both languages
of the paper. -/
theorem meanOdometer_centeredMassLaw_eq (d : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hd : 1 ≤ d) (t : ℕ) :
    meanOdometer (centeredMassLaw d ν) t
      = ∫ ζ, odometerOf ζ t 0 ∂(LatticeProb.iidLaw d ν) := by
  have h1 : ∫ σ, odometerOf (scenery d σ) t 0 ∂(centeredMassLaw d ν)
      = ∫ ζ, odometerOf ζ t 0 ∂((centeredMassLaw d ν).map (scenery d)) :=
    (integral_map (μ := centeredMassLaw d ν) (measurable_scenery d).aemeasurable
      (measurable_odometerOf t 0).aestronglyMeasurable).symm
  have h2 : (centeredMassLaw d ν).map (scenery d) = LatticeProb.iidLaw d ν :=
    map_scenery_centeredMassLaw d ν hd
  unfold meanOdometer
  refine Eq.trans ?_ (Eq.trans h1 (by rw [h2]))
  refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
  exact congrFun (odometer_eq_odometerOf σ t) 0

end Sandpile
