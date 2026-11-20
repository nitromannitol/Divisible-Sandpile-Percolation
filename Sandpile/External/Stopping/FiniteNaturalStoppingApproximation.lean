import Sandpile.External.Stopping.NaturalFiniteStoppingReward

/-!
# Approximation of finite natural stopping times

Finite stopping times of a continuous limiting process can be approximated in
probability by stopping times for uniformly convergent adapted processes.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- Uniform convergence of adapted processes gives finite natural stopping-time
approximations in probability. -/
theorem exists_finite_natural_stopping_approx_inMeasure
    {Ω : Type*} [m : MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℕ → Filtration ℝ≥0 m) (T : ℝ≥0) (V : Finset ℝ≥0)
    (hVT : ∀ t ∈ V, t ≤ T) (τ : Ω → ℝ≥0) (hτV : ∀ ω, τ ω ∈ V)
    (Xn : ℕ → ℝ≥0 → Ω → Continuum.Space d) (X : ℝ≥0 → Ω → Continuum.Space d)
    (hτ : Continuum.IsBrownianStopping X τ)
    (hX : ∀ t, Measurable (X t)) (hXc : ∀ ω, Continuous fun t => X t ω)
    (hXadapt : ∀ n t, @Measurable Ω (Continuum.Space d) (F n t) inferInstance (Xn n t))
    (hpath : ∀ᵐ ω ∂P,
      TendstoUniformlyOn (fun n t => Xn n t ω) (fun t => X t ω) atTop (Set.Icc 0 T)) :
    ∃ τn : ℕ → Ω → ℝ≥0,
      (∀ n, IsStoppingTime (F n) (fun ω => (τn n ω : ℝ≥0∞))) ∧
      (∀ n ω, τn n ω ≤ T) ∧ TendstoInMeasure P τn atTop τ := by
  let O := ℚ → Continuum.Space d
  let := TopologicalSpace.upgradeIsCompletelyMetrizable O
  let Y : ℝ≥0 → Ω → O := rationalHistory X
  let Yn : ℕ → ℝ≥0 → Ω → O := fun n => rationalHistory (Xn n)
  have hYm : ∀ t ∈ V, Measurable (Y t) := by
    intro t ht
    apply measurable_pi_iff.2
    intro q
    exact hX _
  have hYnm : ∀ n, ∀ t ∈ V, @Measurable Ω O (F n t) inferInstance (Yn n t) := by
    intro n t ht
    let : MeasurableSpace Ω := F n t
    apply measurable_pi_iff.2
    intro q
    exact (hXadapt n _).mono ((F n).mono (min_le_right _ _)) le_rfl
  have hYconv : ∀ t ∈ V, ∀ᵐ ω ∂P, Tendsto (fun n => Yn n t ω) atTop (𝓝 (Y t ω)) := by
    intro t ht
    filter_upwards [hpath] with ω hω
    apply tendsto_pi_nhds.2
    intro q
    exact hω.tendsto_at ⟨bot_le, (min_le_right _ _).trans (hVT t ht)⟩
  have hrepresent (t : ℝ≥0) : ∃ S : Set O, MeasurableSet S ∧
      {ω | τ ω = t} = Y t ⁻¹' S := by
    have he := hτ.measurableSet_eq t
    change MeasurableSet[Continuum.brownianFiltration X t] {ω | (τ ω : ℝ≥0∞) = (t : ℝ≥0∞)} at he
    have heq : {ω | (τ ω : ℝ≥0∞) = (t : ℝ≥0∞)} = {ω | τ ω = t} := by
      ext ω
      exact ENNReal.coe_inj
    rw [heq] at he
    obtain ⟨S, hS, heS⟩ := exists_rationalHistory_event X hXc t {ω | τ ω = t} he
    exact ⟨S, hS, heS.symm⟩
  choose S hSm hS using hrepresent
  let p : ℕ → ℝ≥0 → Ω → ℝ := fun n t =>
    P[({ω | τ ω = t} : Set Ω).indicator (fun _ => (1 : ℝ)) | F n t]
  have hpm : ∀ n, ∀ t ∈ V, @Measurable Ω ℝ (F n t) inferInstance (p n t) := by
    intro n t ht
    exact (stronglyMeasurable_condExp (μ := P)).measurable
  have hp : ∀ t ∈ V, TendstoInMeasure P (fun n => p n t) atTop
      (({ω | τ ω = t} : Set Ω).indicator (fun _ => (1 : ℝ))) := by
    intro t ht
    simpa only [p, hS t] using
      tendstoInMeasure_condExp_indicator_of_ae_observations P (fun n => F n t)
        (fun n => (F n).le t) (Y t) (fun n => Yn n t) (hYm t ht)
        (fun n => hYnm n t ht) (hYconv t ht) (S t) (hSm t)
  exact exists_finite_stopping_approx_of_predictors P F T V hVT τ hτV p hpm hp

end Sandpile.External.Stopping
