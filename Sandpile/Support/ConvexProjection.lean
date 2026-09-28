import Sandpile.Support.BinaryProjection
import Sandpile.Support.ConditionalProduct
import Sandpile.Support.FiniteCoord
import Sandpile.Support.IncrementBall

/-! # Convex projection of the box odometer

The convex comparison of an iid scenery with its bounded two-cell conditional
projection. Conditional Jensen is applied to the finite-coordinate odometer,
then the product pushforward and scenery marginal identify both expectations.
-/

open LatticeProb

open MeasureTheory ProbabilityTheory MeasurableSpace

namespace Sandpile

/-- Conditional Jensen for the coordinatewise two-cell projection of a finite product. -/
theorem integral_convex_binaryProjection_le {N : ℕ} (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) {S : Set ℝ} (hS : MeasurableSet S)
    (φ : (Fin N → ℝ) → ℝ) (hφ : ConvexOn ℝ Set.univ φ) (hφ0 : ∀ ξ, 0 ≤ φ ξ)
    (hφi : Integrable φ (Measure.pi fun _ : Fin N => ν)) :
    (∫ ξ, φ (fun i => binaryProjection ν S (ξ i)) ∂(Measure.pi fun _ : Fin N => ν)) ≤
      ∫ ξ, φ ξ ∂(Measure.pi fun _ : Fin N => ν) := by
  classical
  set P := Measure.pi (fun _ : Fin N => ν)
  set m := generateFrom {S}
  letI : MeasurableSpace ℝ := borel ℝ
  set M := productAlg (ι := Fin N) m
  letI : MeasurableSpace (Fin N → ℝ) := @MeasurableSpace.pi (Fin N) (fun _ => ℝ) (fun _ => borel ℝ)
  set g := binaryProjection ν S
  have hm : m ≤ borel ℝ := generateFrom_singleton_le hS
  have hM : M ≤ @MeasurableSpace.pi (Fin N) (fun _ => ℝ) (fun _ => borel ℝ) := productAlg_le hm
  have hId : Integrable (id : (Fin N → ℝ) → (Fin N → ℝ)) P :=
    integrable_pi_iff.mpr fun i => integrable_eval (μ := fun _ : Fin N => ν) hint
  have hi (i : Fin N) : ∀ᵐ ξ ∂P, (P[id | M] ξ) i = (ν[id | m]) (ξ i) := by
    let T : (Fin N → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
    have h1 := T.comp_condExp_comm (m := M) hId
    have h2 := condExp_infinitePi_coordinate ν m hm hint i
    rw [Measure.infinitePi_eq_pi] at h2
    exact h1.trans h2
  have hg (i : Fin N) : ∀ᵐ ξ ∂P, (ν[id | m]) (ξ i) = g (ξ i) := by
    have he := (binaryProjection_ae_eq_condExp ν hint hS).symm
    have hmp := measurePreserving_eval (fun _ : Fin N => ν) i
    have he' : ∀ᵐ z ∂P.map (fun ξ : Fin N → ℝ => ξ i), (ν[id | m]) z = g z := by
      rw [hmp.map_eq]
      exact he
    exact ae_of_ae_map (measurable_pi_apply i).aemeasurable he'
  have hvec : ∀ᵐ ξ ∂P, P[id | M] ξ = fun i => g (ξ i) := by
    have hall : ∀ i : Fin N, ∀ᵐ ξ ∂P, (P[id | M] ξ) i = g (ξ i) := by
      intro i
      filter_upwards [hi i, hg i] with ξ h1 h2
      exact h1.trans h2
    filter_upwards [ae_all_iff.mpr hall] with ξ hξ
    exact funext hξ
  have hj := hφ.map_condExp_le_of_finiteDimensional (μ := P) hM hId hφi
  have hbound : (fun ξ => φ (fun i => g (ξ i))) ≤ᵐ[P] P[φ | M] := by
    filter_upwards [hvec, hj] with ξ hξ hjξ
    change φ (P[id | M] ξ) ≤ P[φ | M] ξ at hjξ
    rwa [hξ] at hjξ
  have h := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun ξ : Fin N → ℝ => hφ0 (fun i => g (ξ i)))
    integrable_condExp hbound
  rwa [integral_condExp hM] at h

/-- `siteExtend s` bundled as a linear map `(Fin s.card → ℝ) →ₗ[ℝ] (Site d → ℝ)`;
additivity and scalar-homogeneity hold by cases on membership in `s`, since
`siteExtend` returns `0` off `s`. -/
noncomputable def siteExtendLinear {d : ℕ} (s : Finset (Site d)) :
    (Fin s.card → ℝ) →ₗ[ℝ] (Site d → ℝ) where
  toFun := siteExtend s
  map_add' := by
    intro ξ η
    funext z
    classical
    by_cases hz : z ∈ s <;> simp [siteExtend, hz]
  map_smul' := by
    intro a ξ
    funext z
    classical
    by_cases hz : z ∈ s <;> simp [siteExtend, hz]

/-- `boxOdometer t x` is convex on `Fin (boxFinset x t).card → ℝ`, obtained by composing
the convexity of `odometerOf` with the linear extension `siteExtendLinear`. -/
theorem convexOn_boxOdometer {d : ℕ} (t : ℕ) (x : Site d) :
    ConvexOn ℝ Set.univ (boxOdometer t x) :=
  (odometerOf_convexOn t x).comp_linearMap (siteExtendLinear (boxFinset x t))

/-- `boxOdometer t x` is integrable against the product law `Measure.pi fun _ => ν` on the
finite coordinate set `boxFinset x t`, transferred from `integrable_odometerOf` through the
coordinate-pick measure-preserving map. -/
theorem integrable_boxOdometer {d : ℕ} (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hpos : Integrable (fun z => max z 0) ν) (t : ℕ) (x : Site d) :
    Integrable (boxOdometer t x) (Measure.pi fun _ : Fin (boxFinset x t).card => ν) := by
  have hmp := LatticeProb.measurePreserving_pick _ ν (boxEnum x t) (boxEnum_injective x t)
  apply (hmp.integrable_comp (measurable_boxOdometer t x).aestronglyMeasurable).mp
  simpa only [Function.comp_def, boxOdometer_pick] using integrable_odometerOf d ν hpos t x

/-- Projecting the scenery onto two cells can only decrease the expected odometer. -/
theorem meanOdometerOf_binaryProjection_le {d : ℕ} (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) {S : Set ℝ} (hS : MeasurableSet S) (t : ℕ) (x : Site d) :
    (∫ ζ, odometerOf ζ t x ∂(LatticeProb.iidLaw d (ν.map (binaryProjection ν S)))) ≤
      ∫ ζ, odometerOf ζ t x ∂(LatticeProb.iidLaw d ν) := by
  set f := binaryProjection ν S
  have hfm : Measurable f := measurable_binaryProjection ν hS
  haveI : IsProbabilityMeasure (ν.map f) := Measure.isProbabilityMeasure_map hfm.aemeasurable
  have hpos : Integrable (fun z : ℝ => max z 0) ν :=
    hint.abs.mono' (by fun_prop) (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right z 0)]
      exact max_le (le_abs_self z) (abs_nonneg z))
  have hj := integral_convex_binaryProjection_le ν hint hS (boxOdometer t x)
    (convexOn_boxOdometer t x) (fun ξ => odometerOf_nonneg _ t x)
    (integrable_boxOdometer ν hpos t x)
  have hmap : (Measure.pi fun _ : Fin (boxFinset x t).card => ν).map (fun ξ i => f (ξ i)) =
      Measure.pi (fun _ : Fin (boxFinset x t).card => ν.map f) :=
    Measure.pi_map_pi (fun _ => hfm.aemeasurable)
  have hleft : (∫ ξ, boxOdometer t x (fun i => f (ξ i))
        ∂(Measure.pi fun _ : Fin (boxFinset x t).card => ν)) =
      ∫ ζ, odometerOf ζ t x ∂(LatticeProb.iidLaw d (ν.map f)) := by
    have hFm : Measurable (fun ξ : Fin (boxFinset x t).card → ℝ => fun i => f (ξ i)) :=
      measurable_pi_lambda _ fun i => hfm.comp (measurable_pi_apply i)
    have hmapint := integral_map (μ := Measure.pi fun _ : Fin (boxFinset x t).card => ν)
      (φ := fun ξ : Fin (boxFinset x t).card → ℝ => fun i => f (ξ i))
      (f := boxOdometer t x) hFm.aemeasurable
      (by rw [hmap]; exact (measurable_boxOdometer t x).aestronglyMeasurable)
    rw [hmap] at hmapint
    rw [← hmapint]
    rw [← integral_pick (ν.map f) (boxEnum x t) (boxEnum_injective x t) (boxOdometer t x)
      (measurable_boxOdometer t x).aestronglyMeasurable]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ζ => boxOdometer_pick t x ζ)
  have hright : (∫ ξ, boxOdometer t x ξ ∂(Measure.pi fun _ : Fin (boxFinset x t).card => ν)) =
      ∫ ζ, odometerOf ζ t x ∂(LatticeProb.iidLaw d ν) := by
    rw [← integral_pick ν (boxEnum x t) (boxEnum_injective x t) (boxOdometer t x)
      (measurable_boxOdometer t x).aestronglyMeasurable]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ζ => boxOdometer_pick t x ζ)
  rw [hleft, hright] at hj
  exact hj

end Sandpile
