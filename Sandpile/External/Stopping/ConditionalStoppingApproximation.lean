import Sandpile.External.Stopping.ConditionalPredictorConvergence

/-!
# Approximation of finite stopping times by conditional predictions

Conditional expectations of the equality events yield the finite stopping
approximations used in Coquet and Toldo, Section 2.2, once those events admit
L¹ approximations measurable in the approximating filtrations.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- L¹ approximations of the equality events give bounded stopping times that
converge in probability, through the conditional predictors of those events. -/
theorem exists_finite_stopping_approx_of_l1_events
    {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℕ → Filtration ℝ≥0 m) (T : ℝ≥0) (V : Finset ℝ≥0)
    (hVT : ∀ t ∈ V, t ≤ T) (τ : Ω → ℝ≥0) (hτm : Measurable τ) (hτV : ∀ ω, τ ω ∈ V)
    (g : ℕ → ℝ≥0 → Ω → ℝ)
    (hg : ∀ n, ∀ t ∈ V, Integrable (g n t) P)
    (hgm : ∀ n, ∀ t ∈ V, StronglyMeasurable[F n t] (g n t))
    (hlim : ∀ t ∈ V, Tendsto (fun n => eLpNorm
      (({ω | τ ω = t} : Set Ω).indicator (fun _ => (1 : ℝ)) - g n t) 1 P) atTop (𝓝 0)) :
    ∃ τn : ℕ → Ω → ℝ≥0,
      (∀ n, IsStoppingTime (F n) (fun ω => (τn n ω : ℝ≥0∞))) ∧
      (∀ n ω, τn n ω ≤ T) ∧ TendstoInMeasure P τn atTop τ := by
  let p : ℕ → ℝ≥0 → Ω → ℝ := fun n t =>
    P[({ω | τ ω = t} : Set Ω).indicator (fun _ => (1 : ℝ)) | F n t]
  apply exists_finite_stopping_approx_of_predictors P F T V hVT τ hτV p
  · intro n t ht
    exact (stronglyMeasurable_condExp (μ := P)).measurable
  · intro t ht
    have hset : MeasurableSet {ω | τ ω = t} := measurableSet_eq_fun hτm measurable_const
    have hi : Integrable (({ω | τ ω = t} : Set Ω).indicator (fun _ => (1 : ℝ))) P :=
      (integrable_const (1 : ℝ)).indicator hset
    exact tendstoInMeasure_condExp_of_l1_approx P (fun n => F n t)
      (fun n => (F n).le t) _ hi (fun n => g n t) (fun n => hg n t ht)
      (fun n => hgm n t ht) (hlim t ht)

end Sandpile.External.Stopping
