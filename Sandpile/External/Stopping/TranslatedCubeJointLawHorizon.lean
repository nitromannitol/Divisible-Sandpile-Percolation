import Sandpile.External.Stopping.TranslatedCubeJointLawReward

/-!
# Cube rewards with almost-sure horizon bounds

An equal-law randomized stopping representation can be clipped to a horizon
that bounds its clock almost surely.
-/

open MeasureTheory Filter unitInterval
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- The same reward bound holds when the clock is bounded by the horizon
almost surely, even if its stopping realization is only pointwise bounded by
a larger horizon. -/
theorem integral_joint_clock_reward_le_translated_brownian_cube_of_ae_le {d : ℕ} [NeZero d]
    (ρ : Measure (C(ℝ≥0, Continuum.Space d) × I)) [IsProbabilityMeasure ρ]
    (a : Continuum.Space d) (clock : I → ℝ≥0) (hclock : Measurable clock) (T : ℝ≥0)
    (hB : Continuum.IsBrownian d a (fun t (f : C(ℝ≥0, Continuum.Space d)) => f t) ρ.fst)
    (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ t z, |G t z| ≤ M)
    (τ : C(ℝ≥0, Continuum.Space d) × I → ℝ≥0)
    (hτ : IsStoppingTime (parameterFiltration (pathFiltration (d := d))).rightCont
      (fun p => (τ p : ℝ≥0∞)))
    (hmap : (ρ.fst.prod volume).map (fun p => (p.1, τ p)) =
      ρ.map (fun p => (p.1, clock p.2)))
    (hclockT : ∀ᵐ p ∂ρ, clock p.2 ≤ T)
    (hkill : ∀ᵐ p ∂ρ, (p.1, clock p.2) ∈ translatedCubeConstrainedPaths a 1) :
    (∫ p, G ((T : ℝ) - (clock p.2 : ℝ)) (p.1 (clock p.2)) ∂ρ) ≤
      Continuum.brownianDiscountCube (fun t (f : C(ℝ≥0, Continuum.Space d)) => f t)
        ρ.fst (fun s z => -G s z) T 1 a := by
  have hτm : Measurable τ := measurable_coe_nnreal_ennreal_iff.mp
    (hτ.measurable.mono hτ.measurableSpace_le le_rfl)
  have hJ : Measurable (fun p : C(ℝ≥0, Continuum.Space d) × I => (p.1, τ p)) :=
    measurable_fst.prodMk hτm
  have hJ' : Measurable (fun p : C(ℝ≥0, Continuum.Space d) × I =>
      (p.1, clock p.2)) := measurable_fst.prodMk (hclock.comp measurable_snd)
  have hbound : ∀ᵐ p ∂ρ.map (fun p => (p.1, clock p.2)), p.2 ≤ T := by
    apply (ae_map_iff hJ'.aemeasurable (measurableSet_le measurable_snd measurable_const)).2
    exact hclockT
  rw [← hmap] at hbound
  have hτae : ∀ᵐ p ∂(ρ.fst.prod volume), τ p ≤ T :=
    ae_of_ae_map hJ.aemeasurable hbound
  have hclip : IsStoppingTime (parameterFiltration (pathFiltration (d := d))).rightCont
      (fun p => ((min (τ p) T : ℝ≥0) : ℝ≥0∞)) := by
    have heq : (fun p => ((min (τ p) T : ℝ≥0) : ℝ≥0∞)) =
        (fun p => min ((τ p : ℝ≥0) : ℝ≥0∞) (T : ℝ≥0∞)) := by
      funext p
      exact ENNReal.coe_min _ _
    rw [heq]
    exact hτ.min_const T
  have hmap' : (ρ.fst.prod volume).map (fun p => (p.1, min (τ p) T)) =
      ρ.map (fun p => (p.1, clock p.2)) := by
    calc
      _ = (ρ.fst.prod volume).map (fun p => (p.1, τ p)) := by
        apply Measure.map_congr
        filter_upwards [hτae] with p hp
        rw [min_eq_left hp]
      _ = _ := hmap
  exact integral_joint_clock_reward_le_translated_brownian_cube ρ a clock hclock T hB G hGc M hG
    (fun p => min (τ p) T) hclip (fun p => min_le_right _ _) hmap' hkill


end Sandpile.External.Stopping
