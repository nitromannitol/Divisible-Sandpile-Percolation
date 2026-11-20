import Sandpile.External.Stopping.RandomizedRightCubeValue
import Sandpile.External.Stopping.RandomizedCubeConstraint
import Sandpile.External.Stopping.PathClockCausality

/-!
# Cube-killed rewards of randomized joint laws

A path-clock law represented by a randomized stopping time has reward bounded
by the Brownian cube-stopping value when its paths satisfy the cube constraint.
-/

open MeasureTheory Filter unitInterval
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- A represented path-clock law satisfying the pre-stop cube constraint has
reward at most the Brownian cube-stopping value. -/
theorem integral_joint_clock_reward_le_brownian_cube
    {d : ℕ} [NeZero d] (ρ : Measure (C(ℝ≥0, Continuum.Space d) × I))
    [IsProbabilityMeasure ρ]
    (hB : Continuum.IsBrownian d 0 (fun t (f : C(ℝ≥0, Continuum.Space d)) => f t) ρ.fst)
    (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ t z, |G t z| ≤ M)
    (τ : C(ℝ≥0, Continuum.Space d) × I → ℝ≥0)
    (hτ : IsStoppingTime (parameterFiltration (pathFiltration (d := d))).rightCont
      (fun p => (τ p : ℝ≥0∞))) (hτ1 : ∀ p, τ p ≤ 1)
    (hmap : (ρ.fst.prod volume).map (fun p => (p.1, τ p)) =
      ρ.map (fun p => (p.1, unitClock id p.2)))
    (hkill : ∀ᵐ p ∂ρ, (p.1, unitClock id p.2) ∈ cubeConstrainedPaths (d := d) 1) :
    (∫ p, G (1 - (unitClock id p.2 : ℝ)) (p.1 (unitClock id p.2)) ∂ρ) ≤
      Continuum.brownianDiscountCube (fun t (f : C(ℝ≥0, Continuum.Space d)) => f t)
        ρ.fst (fun s z => -G s z) 1 1 0 := by
  let E : ℝ≥0 → C(ℝ≥0, Continuum.Space d) → Continuum.Space d := fun t f => f t
  have hτm : Measurable τ := measurable_coe_nnreal_ennreal_iff.mp
    (hτ.measurable.mono hτ.measurableSpace_le le_rfl)
  have hJ : Measurable (fun p : C(ℝ≥0, Continuum.Space d) × I => (p.1, τ p)) :=
    measurable_fst.prodMk hτm
  have hunit : Measurable (unitClock (id : I → I)) := by
    change Measurable (fun u : I => (⟨(u : ℝ), u.2.1⟩ : ℝ≥0))
    exact (measurable_subtype_coe : Measurable (fun u : I => (u : ℝ))).subtype_mk
  have hJ' : Measurable (fun p : C(ℝ≥0, Continuum.Space d) × I =>
      (p.1, unitClock id p.2)) := measurable_fst.prodMk (hunit.comp measurable_snd)
  have hkill' : ∀ᵐ p ∂(ρ.fst.prod volume), (p.1, τ p) ∈ cubeConstrainedPaths (d := d) 1 := by
    have hmapkill : ∀ᵐ p ∂ρ.map (fun p => (p.1, unitClock id p.2)),
        p ∈ cubeConstrainedPaths (d := d) 1 := by
      change ∀ᵐ p : C(ℝ≥0, Continuum.Space d) × ℝ≥0 ∂ρ.map (fun p => (p.1, unitClock id p.2)),
        ∀ t < p.2, ∀ i, |p.1 t i| ≤ 1
      rw [ae_map_iff hJ'.aemeasurable (isClosed_cubeConstrainedPaths (d := d) 1).measurableSet]
      exact hkill
    rw [← hmap] at hmapkill
    exact ae_of_ae_map hJ.aemeasurable hmapkill
  have hbefore := ae_randomized_time_le_cube_exit ρ.fst volume id hB 1 τ hτ1 hkill'
  have hpos : Measurable (fun p : C(ℝ≥0, Continuum.Space d) × ℝ≥0 => p.1 p.2) :=
    continuous_eval.measurable
  let F : C(ℝ≥0, Continuum.Space d) × ℝ≥0 → ℝ := fun p => G (1 - (p.2 : ℝ)) (p.1 p.2)
  have hFm : Measurable F := hGc.measurable.comp
    ((measurable_const.sub (measurable_coe_nnreal_real.comp measurable_snd)).prodMk hpos)
  have hi : Integrable (fun p : C(ℝ≥0, Continuum.Space d) × I =>
      G (1 - (τ p : ℝ)) (p.1 (τ p))) (ρ.fst.prod volume) := by
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
  have hbound := integral_parameter_rightCont_stopping_le_brownianDiscountCube ρ.fst volume 0 E hB
    (fun t => (continuous_eval_const t).measurable) (fun f => f.continuous) 1 G hGc M hG τ
    hτ' hτ1 hbefore hi
  have heq : (∫ p, G (1 - (unitClock id p.2 : ℝ)) (p.1 (unitClock id p.2)) ∂ρ) =
      ∫ p, G (1 - (τ p : ℝ)) (p.1 (τ p)) ∂(ρ.fst.prod volume) := by
    change (∫ p, F (p.1, unitClock id p.2) ∂ρ) = ∫ p, F (p.1, τ p) ∂(ρ.fst.prod volume)
    rw [← integral_map hJ'.aemeasurable hFm.aestronglyMeasurable,
      ← integral_map hJ.aemeasurable hFm.aestronglyMeasurable, hmap]
  rw [heq]
  exact hbound

end Sandpile.External.Stopping
