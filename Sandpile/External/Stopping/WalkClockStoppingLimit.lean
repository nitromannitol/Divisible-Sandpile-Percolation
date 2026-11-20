import Sandpile.External.Stopping.ScaledClockCausality

/-!
# Stopping realizations of walk-clock limits

A joint weak limit of interpolated walks and normalized discrete stopping
clocks has an equal-law randomized stopping realization on continuous-path
space, at any positive physical horizon.
-/

open MeasureTheory ProbabilityTheory Filter Topology unitInterval
open scoped NNReal ENNReal ProbabilityTheory

namespace Sandpile.External.Stopping

/-- Viewing a unit-interval clock as a nonnegative time is continuous. -/
theorem continuous_unitClock : Continuous (unitClock (id : I → I)) := by
  change Continuous (fun u : I => (⟨(u : ℝ), u.2.1⟩ : ℝ≥0))
  exact (continuous_subtype_val : Continuous (fun u : I => (u : ℝ))).subtype_mk _

/-- Any normalized joint weak limit of interpolated walks and discrete stopping
clocks has an equal-law bounded randomized stopping realization. -/
theorem exists_stopping_version_of_walk_clock_limit {d : ℕ} [NeZero d]
    {ι : Type*} [Countable ι]
    (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) (q : ℕ → Site d)
    (τ : ℕ → (ℕ → Site d) → ℕ) (hτ : ∀ n, IsWalkStopping (τ n))
    (hτm : ∀ n, Measurable (τ n))
    (θ : ℕ → (ℕ → Site d) → I) (hθ : ∀ n, Measurable (θ n))
    (c : ℝ≥0) (hc : 0 < c)
    (hdecode : ∀ n X, c * unitClock id (θ n X) = diffusiveLatticeClock (R n) (τ n X))
    (μ : ℕ → ProbabilityMeasure (C(ℝ≥0, Continuum.Space d) × I))
    (ρ : ProbabilityMeasure (C(ℝ≥0, Continuum.Space d) × I))
    (hμ : ∀ n, (μ n : Measure _) = (walkLaw d (q n)).map
      (fun X => (diffusiveWalkPath (R n) X, θ n X)))
    (hlim : Tendsto μ atTop (𝓝 ρ)) (time : ι → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b → ∃ i, a < time i ∧ time i < b) :
    ∃ sigma : C(ℝ≥0, Continuum.Space d) × I → ℝ≥0,
      IsStoppingTime (parameterFiltration (pathFiltration (d := d))).rightCont
        (fun p => (sigma p : ℝ≥0∞)) ∧
      (∀ p, sigma p ≤ c) ∧
      ((ρ : Measure (C(ℝ≥0, Continuum.Space d) × I)).fst.prod volume).map (fun p => (p.1, sigma p)) =
        (ρ : Measure (C(ℝ≥0, Continuum.Space d) × I)).map (fun p => (p.1, c * unitClock id p.2)) := by
  have hclock : Continuous (fun z : I => c * unitClock id z) :=
    continuous_const.mul continuous_unitClock
  have hind (t : ℝ≥0) :=
    indepFun_future_stopped_of_parameterized_walk_joint_weak_limit R hR q τ hτ hτm
      θ hθ (fun z => c * unitClock id z) hclock hdecode μ ρ hμ hlim t
  exact exists_scaled_path_stopping_version (ρ : Measure (C(ℝ≥0, Continuum.Space d) × I)) c hc hind time hdense

end Sandpile.External.Stopping
