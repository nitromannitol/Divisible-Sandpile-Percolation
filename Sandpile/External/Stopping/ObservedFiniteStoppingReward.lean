import Sandpile.External.Stopping.ObservationEventPredictors
import Sandpile.External.Stopping.ConvergentStoppingRewards

/-!
# Finite stopping rewards from convergent observations

Borel descriptions of finite stopping events and almost surely convergent
adapted observations produce the conditional stopping approximations in
Coquet and Toldo, Section 2.2.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- Finite stopping rewards can be approximated whenever their equality events
are Borel events of convergent adapted observations. -/
theorem exists_finite_stopping_reward_approx_of_observations
    {Ω E O : Type*} [m : MeasurableSpace Ω]
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [MetricSpace O] [SecondCountableTopology O] [MeasurableSpace O] [BorelSpace O]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℕ → Filtration ℝ≥0 m) (T : ℝ≥0) (V : Finset ℝ≥0)
    (hVT : ∀ t ∈ V, t ≤ T) (τ : Ω → ℝ≥0) (hτV : ∀ ω, τ ω ∈ V)
    (Y : ℝ≥0 → Ω → O) (Yn : ℕ → ℝ≥0 → Ω → O)
    (hYm : ∀ t ∈ V, Measurable (Y t))
    (hYnm : ∀ n, ∀ t ∈ V, @Measurable Ω O (F n t) inferInstance (Yn n t))
    (hYconv : ∀ t ∈ V, ∀ᵐ ω ∂P, Tendsto (fun n => Yn n t ω) atTop (𝓝 (Y t ω)))
    (S : ℝ≥0 → Set O) (hSm : ∀ t ∈ V, MeasurableSet (S t))
    (hS : ∀ t ∈ V, {ω | τ ω = t} = Y t ⁻¹' S t)
    (Xn : ℕ → ℝ≥0 → Ω → E) (X : ℝ≥0 → Ω → E)
    (hXn : ∀ n, Measurable (fun p : ℝ≥0 × Ω => Xn n p.1 p.2))
    (hpath : ∀ᵐ ω ∂P, Continuous (fun t => X t ω) ∧
      TendstoUniformlyOn (fun n t => Xn n t ω) (fun t => X t ω) atTop (Set.Icc 0 T))
    (G : ℝ≥0 → E → ℝ) (hGc : Continuous (fun p : ℝ≥0 × E => G p.1 p.2))
    (M : ℝ) (hG : ∀ t z, |G t z| ≤ M) :
    ∃ τn : ℕ → Ω → ℝ≥0,
      (∀ n, IsStoppingTime (F n) (fun ω => (τn n ω : ℝ≥0∞))) ∧
      (∀ n ω, τn n ω ≤ T) ∧
      Tendsto (fun n => ∫ ω, G (τn n ω) (Xn n (τn n ω) ω) ∂P) atTop
        (𝓝 (∫ ω, G (τ ω) (X (τ ω) ω) ∂P)) := by
  let p : ℕ → ℝ≥0 → Ω → ℝ := fun n t =>
    P[({ω | τ ω = t} : Set Ω).indicator (fun _ => (1 : ℝ)) | F n t]
  have hpm : ∀ n, ∀ t ∈ V, @Measurable Ω ℝ (F n t) inferInstance (p n t) := by
    intro n t ht
    exact (stronglyMeasurable_condExp (μ := P)).measurable
  have hp : ∀ t ∈ V, TendstoInMeasure P (fun n => p n t) atTop
      (({ω | τ ω = t} : Set Ω).indicator (fun _ => (1 : ℝ))) := by
    intro t ht
    simpa only [p, hS t ht] using
      tendstoInMeasure_condExp_indicator_of_ae_observations P (fun n => F n t)
        (fun n => (F n).le t) (Y t) (fun n => Yn n t) (hYm t ht)
        (fun n => hYnm n t ht) (hYconv t ht) (S t) (hSm t ht)
  obtain ⟨τn, hτn, hτnT, hτlim⟩ :=
    exists_finite_stopping_approx_of_predictors P F T V hVT τ hτV p hpm hp
  have hτnm : ∀ n, Measurable (τn n) := by
    intro n
    exact measurable_coe_nnreal_ennreal_iff.mp
      ((hτn n).measurable.mono (hτn n).measurableSpace_le le_rfl)
  have hXstop : ∀ n, AEMeasurable (fun ω => Xn n (τn n ω) ω) P := fun n =>
    ((hXn n).comp ((hτnm n).prodMk measurable_id)).aemeasurable
  exact ⟨τn, hτn, hτnT, tendsto_integral_reward_of_uniform_paths_and_stops P Xn X T τn τ
    (fun n => (hτnm n).aemeasurable) hXstop hτnT hτlim hpath G hGc M hG⟩

end Sandpile.External.Stopping
