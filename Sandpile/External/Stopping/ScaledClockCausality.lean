import Sandpile.External.Stopping.ScaledClockFiltration

/-!
# Causality of normalized clock distributions

The conditional distribution of a normalized clock is adapted to the
physical path filtration observed on the corresponding scaled time axis.
-/

open MeasureTheory ProbabilityTheory Set Filter unitInterval
open scoped NNReal ENNReal ProbabilityTheory

namespace Sandpile.External.Stopping

/-- A unit-interval clock is a measurable nonnegative time. -/
theorem measurable_unitClock : Measurable (unitClock (id : I → I)) := by
  change Measurable (fun u : I => (⟨(u : ℝ), u.2.1⟩ : ℝ≥0))
  exact (measurable_subtype_coe : Measurable (fun u : I => (u : ℝ))).subtype_mk

/-- A positive scale does not change normalized clock sublevel events. -/
theorem scaled_unitClock_event {Ω : Type*} (c : ℝ≥0) (hc : 0 < c)
    (τ : Ω → I) (s : ℝ≥0) :
    {ω | c * unitClock τ ω ≤ c * s} = τ ⁻¹' Icc 0 (unitTime s) := by
  ext ω
  simp only [mem_ofPred_eq, mem_preimage, mem_Icc]
  rw [mul_le_mul_iff_right₀ hc, unitClock_le_iff]
  exact ⟨fun h => ⟨by exact (τ ω).2.1, h⟩, And.right⟩

/-- Future independence implies an adapted conditional CDF for the normalized
clock in the path filtration scaled by the positive physical horizon. -/
theorem exists_scaled_path_kernel_event_version {d : ℕ}
    (ρ : Measure (C(ℝ≥0, Continuum.Space d) × I)) [IsProbabilityMeasure ρ]
    (c : ℝ≥0) (hc : 0 < c)
    (hind : ∀ u : ℝ≥0, IndepFun (fun p => futureIncrementPath u p.1)
      (fun p => (LatticeProb.stoppedPath (u : ℝ≥0∞) p.1,
        min (c * unitClock id p.2) u)) ρ)
    (s : ℝ≥0) :
    ∃ f : C(ℝ≥0, Continuum.Space d) → ℝ,
      @Measurable C(ℝ≥0, Continuum.Space d) ℝ
        ((scaledFiltration (pathFiltration (d := d)) c) s) inferInstance f ∧
      f =ᵐ[ρ.fst] fun ω => (ρ.condKernel ω).real (Icc 0 (unitTime s)) := by
  have hτm : Measurable (fun p : C(ℝ≥0, Continuum.Space d) × I =>
      c * unitClock id p.2) :=
    measurable_const.mul (measurable_unitClock.comp measurable_snd)
  have hi := indep_future_pathPast_clockEvent ρ Prod.fst
    (fun p => c * unitClock id p.2) measurable_fst hτm hind (c * s) (c * s) le_rfl
  have hevent : {p : C(ℝ≥0, Continuum.Space d) × I | c * unitClock id p.2 ≤ c * s} =
      Prod.snd ⁻¹' Icc 0 (unitTime s) := by
    change {p | c * unitClock (Prod.snd : C(ℝ≥0, Continuum.Space d) × I → I) p ≤ c * s} = _
    exact scaled_unitClock_event c hc Prod.snd s
  rw [hevent] at hi
  apply exists_kernel_event_version_of_independent_future ρ
    (scaledFiltration (pathFiltration (d := d)) c) s (Icc 0 (unitTime s)) measurableSet_Icc
    ((pathFutureSigma (d := d) (c * s)).comap Prod.fst)
  · have hfuture : pathFutureSigma (d := d) (c * s) ≤
        (inferInstance : MeasurableSpace C(ℝ≥0, Continuum.Space d)) := by
      rw [← pathPastSigma_sup_pathFutureSigma (c * s)]
      exact le_sup_right
    exact (MeasurableSpace.comap_mono hfuture).trans measurable_fst.comap_le
  · change _ = (pathFutureSigma (c * s)).comap Prod.fst ⊔
      ((pathFiltration (d := d)) (c * s)).comap Prod.fst
    rw [pathFiltration_eq_pathPastSigma, ← MeasurableSpace.comap_sup,
      sup_comm, pathPastSigma_sup_pathFutureSigma]
    rfl
  · simpa only [scaledFiltration, pathFiltration_eq_pathPastSigma] using hi

/-- A causal normalized path-clock law has an equal-law randomized stopping
realization at any positive physical horizon. -/
theorem exists_scaled_path_stopping_version {d : ℕ} {ι : Type*} [Countable ι]
    (ρ : Measure (C(ℝ≥0, Continuum.Space d) × I)) [IsProbabilityMeasure ρ]
    (c : ℝ≥0) (hc : 0 < c)
    (hind : ∀ u : ℝ≥0, IndepFun (fun p => futureIncrementPath u p.1)
      (fun p => (LatticeProb.stoppedPath (u : ℝ≥0∞) p.1,
        min (c * unitClock id p.2) u)) ρ)
    (time : ι → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b → ∃ i, a < time i ∧ time i < b) :
    ∃ τ : C(ℝ≥0, Continuum.Space d) × I → ℝ≥0,
      IsStoppingTime (parameterFiltration (pathFiltration (d := d))).rightCont
        (fun p => (τ p : ℝ≥0∞)) ∧
      (∀ p, τ p ≤ c) ∧
      (ρ.fst.prod volume).map (fun p => (p.1, τ p)) =
        ρ.map (fun p => (p.1, c * unitClock id p.2)) := by
  obtain ⟨sigma, hsigma, hsigma1, hlaw⟩ := exists_stopping_version_of_joint_law
    (scaledFiltration (pathFiltration (d := d)) c) ρ time hdense
      (fun i => exists_scaled_path_kernel_event_version ρ c hc hind (time i))
  have hsigmastop : IsStoppingTime
      (scaledFiltration (parameterFiltration (A := I) (pathFiltration (d := d))) c).rightCont
      (fun p => (sigma p : ℝ≥0∞)) := by
    simpa only [parameterFiltration_scaledFiltration] using hsigma
  have hsigmam : Measurable sigma := measurable_coe_nnreal_ennreal_iff.1
    (hsigma.measurable.mono hsigma.measurableSpace_le le_rfl)
  let D : C(ℝ≥0, Continuum.Space d) × ℝ≥0 → C(ℝ≥0, Continuum.Space d) × ℝ≥0 :=
    fun p => (p.1, c * p.2)
  have hD : Measurable D := measurable_fst.prodMk (measurable_const.mul measurable_snd)
  have hunit : Measurable (fun p : C(ℝ≥0, Continuum.Space d) × I =>
      (p.1, unitClock id p.2)) := measurable_fst.prodMk
        (measurable_unitClock.comp measurable_snd)
  refine ⟨fun p => c * sigma p, ?_, ?_, ?_⟩
  · exact isStoppingTime_mul_scaledFiltration_rightCont _ c hc sigma hsigmastop
  · intro p
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hsigma1 p) (zero_le : 0 ≤ c)
  · calc
      _ = ((ρ.fst.prod volume).map (fun p => (p.1, sigma p))).map D := by
        rw [Measure.map_map hD (measurable_fst.prodMk hsigmam)]
        rfl
      _ = (ρ.map (fun p => (p.1, unitClock id p.2))).map D := by rw [hlaw]
      _ = _ := by rw [Measure.map_map hD hunit]; rfl

end Sandpile.External.Stopping
