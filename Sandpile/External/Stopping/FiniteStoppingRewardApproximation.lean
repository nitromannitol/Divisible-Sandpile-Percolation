import Sandpile.External.Stopping.ConvergentStoppingRewards

/-!
# Finite stopping reward approximation

The conditional-event construction and stopped-reward convergence combine to
approximate any finite stopping reward when adapted L¹ event approximants and
uniformly converging sample paths are available.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- A finite stopping reward can be approximated by stopping rewards for the
approximating filtrations under adapted L¹ approximation of its event slices. -/
theorem exists_finite_stopping_reward_approx_of_l1_events
    {Ω E : Type*} [m : MeasurableSpace Ω] [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℕ → Filtration ℝ≥0 m) (T : ℝ≥0) (V : Finset ℝ≥0)
    (hVT : ∀ t ∈ V, t ≤ T) (τ : Ω → ℝ≥0) (hτm : Measurable τ) (hτV : ∀ ω, τ ω ∈ V)
    (g : ℕ → ℝ≥0 → Ω → ℝ)
    (hg : ∀ n, ∀ t ∈ V, Integrable (g n t) P)
    (hgm : ∀ n, ∀ t ∈ V, StronglyMeasurable[F n t] (g n t))
    (hlim : ∀ t ∈ V, Tendsto (fun n => eLpNorm
      (({ω | τ ω = t} : Set Ω).indicator (fun _ => (1 : ℝ)) - g n t) 1 P) atTop (𝓝 0))
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
  obtain ⟨τn, hτn, hτnT, hτlim⟩ :=
    exists_finite_stopping_approx_of_l1_events P F T V hVT τ hτm hτV g hg hgm hlim
  have hτnm : ∀ n, Measurable (τn n) := by
    intro n
    exact measurable_coe_nnreal_ennreal_iff.mp
      ((hτn n).measurable.mono (hτn n).measurableSpace_le le_rfl)
  have hYn : ∀ n, AEMeasurable (fun ω => Xn n (τn n ω) ω) P := fun n =>
    ((hXn n).comp ((hτnm n).prodMk measurable_id)).aemeasurable
  exact ⟨τn, hτn, hτnT, tendsto_integral_reward_of_uniform_paths_and_stops P Xn X T τn τ
    (fun n => (hτnm n).aemeasurable) hYn hτnT hτlim hpath G hGc M hG⟩

end Sandpile.External.Stopping
