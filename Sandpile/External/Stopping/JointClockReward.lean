import Sandpile.External.Stopping.WalkClockStoppingLimit
import Sandpile.External.Stopping.RandomizedRightFiltrationValue

/-!
# Rewards of represented path-clock laws

A path-clock law represented by a bounded randomized stopping time has reward
at most the natural-filtration stopping value of its path marginal.
-/

open MeasureTheory Filter unitInterval
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- The reward of an equal-law randomized stop is bounded by the stopping
value of the path marginal. -/
theorem integral_joint_clock_reward_le_discount {d : ℕ}
    (ρ : Measure (C(ℝ≥0, Continuum.Space d) × I)) [IsProbabilityMeasure ρ]
    (clock : I → ℝ≥0) (hclock : Measurable clock) (T : ℝ≥0)
    (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ t z, |G t z| ≤ M)
    (τ : C(ℝ≥0, Continuum.Space d) × I → ℝ≥0)
    (hτ : IsStoppingTime (parameterFiltration (pathFiltration (d := d))).rightCont
      (fun p => (τ p : ℝ≥0∞))) (hτT : ∀ p, τ p ≤ T)
    (hmap : (ρ.fst.prod volume).map (fun p => (p.1, τ p)) =
      ρ.map (fun p => (p.1, clock p.2))) :
    (∫ p, G ((T : ℝ) - (clock p.2 : ℝ)) (p.1 (clock p.2)) ∂ρ) ≤
      Continuum.brownianDiscount (fun t (f : C(ℝ≥0, Continuum.Space d)) => f t)
        ρ.fst (fun s z => -G s z) T := by
  let E : ℝ≥0 → C(ℝ≥0, Continuum.Space d) → Continuum.Space d := fun t f => f t
  have hτm : Measurable τ := measurable_coe_nnreal_ennreal_iff.mp
    (hτ.measurable.mono hτ.measurableSpace_le le_rfl)
  have hJ : Measurable (fun p : C(ℝ≥0, Continuum.Space d) × I => (p.1, τ p)) :=
    measurable_fst.prodMk hτm
  have hJ' : Measurable (fun p : C(ℝ≥0, Continuum.Space d) × I =>
      (p.1, clock p.2)) := measurable_fst.prodMk (hclock.comp measurable_snd)
  let F : C(ℝ≥0, Continuum.Space d) × ℝ≥0 → ℝ := fun p =>
    G ((T : ℝ) - (p.2 : ℝ)) (p.1 p.2)
  have hFm : Measurable F := hGc.measurable.comp
    ((measurable_const.sub (measurable_coe_nnreal_real.comp measurable_snd)).prodMk
      continuous_eval.measurable)
  have hi : Integrable (fun p : C(ℝ≥0, Continuum.Space d) × I =>
      G ((T : ℝ) - (τ p : ℝ)) (p.1 (τ p))) (ρ.fst.prod volume) := by
    apply Integrable.of_bound (hFm.comp hJ).aestronglyMeasurable M
    filter_upwards with p
    simpa only [Function.comp_apply, F, Real.norm_eq_abs] using hG _ _
  have hFE (t : ℝ≥0) : (pathFiltration (d := d)) t = Continuum.brownianFiltration E t := by
    rw [pathFiltration_eq_pathPastSigma, pathPastSigma_eq_brownianFiltration]
  have hτ' : IsStoppingTime (parameterFiltration (Continuum.brownianFiltration E)).rightCont
      (fun p => (τ p : ℝ≥0∞)) := by
    intro t
    rw [Filtration.rightCont_eq, MeasurableSpace.measurableSet_iInf]
    intro s
    rw [MeasurableSpace.measurableSet_iInf]
    intro hts
    have hs := hτ t
    rw [Filtration.rightCont_eq, MeasurableSpace.measurableSet_iInf] at hs
    have hs' := (MeasurableSpace.measurableSet_iInf.mp (hs s)) hts
    change MeasurableSet[((pathFiltration (d := d)) s).prod inferInstance] _ at hs'
    change MeasurableSet[(Continuum.brownianFiltration E s).prod inferInstance] _
    rw [← hFE s]
    exact hs'
  have hbound := integral_parameter_rightCont_stopping_le_brownianDiscount ρ.fst volume E
    (fun t => (continuous_eval_const t).measurable.aemeasurable)
    (Filter.Eventually.of_forall fun f => f.continuous) T G hGc M hG τ hτ' hτT hi
  have heq : (∫ p, G ((T : ℝ) - (clock p.2 : ℝ)) (p.1 (clock p.2)) ∂ρ) =
      ∫ p, G ((T : ℝ) - (τ p : ℝ)) (p.1 (τ p)) ∂(ρ.fst.prod volume) := by
    change (∫ p, F (p.1, clock p.2) ∂ρ) = ∫ p, F (p.1, τ p) ∂(ρ.fst.prod volume)
    rw [← integral_map hJ'.aemeasurable hFm.aestronglyMeasurable,
      ← integral_map hJ.aemeasurable hFm.aestronglyMeasurable, hmap]
  rw [heq]
  exact hbound

/-- The same reward bound holds when the clock is bounded by the horizon
almost surely, even if its stopping realization is only pointwise bounded by
a larger horizon. -/
theorem integral_joint_clock_reward_le_discount_of_ae_le {d : ℕ}
    (ρ : Measure (C(ℝ≥0, Continuum.Space d) × I)) [IsProbabilityMeasure ρ]
    (clock : I → ℝ≥0) (hclock : Measurable clock) (T : ℝ≥0)
    (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ t z, |G t z| ≤ M)
    (τ : C(ℝ≥0, Continuum.Space d) × I → ℝ≥0)
    (hτ : IsStoppingTime (parameterFiltration (pathFiltration (d := d))).rightCont
      (fun p => (τ p : ℝ≥0∞)))
    (hmap : (ρ.fst.prod volume).map (fun p => (p.1, τ p)) =
      ρ.map (fun p => (p.1, clock p.2)))
    (hclockT : ∀ᵐ p ∂ρ, clock p.2 ≤ T) :
    (∫ p, G ((T : ℝ) - (clock p.2 : ℝ)) (p.1 (clock p.2)) ∂ρ) ≤
      Continuum.brownianDiscount (fun t (f : C(ℝ≥0, Continuum.Space d)) => f t)
        ρ.fst (fun s z => -G s z) T := by
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
  exact integral_joint_clock_reward_le_discount ρ clock hclock T G hGc M hG
    (fun p => min (τ p) T) hclip (fun p => min_le_right _ _) hmap'

end Sandpile.External.Stopping
