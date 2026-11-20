import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

/-!
# Convergence of stopped process expectations

Bounded random times may be passed through a continuous process and its
expectation when the process has an integrable pathwise envelope.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

/-- A continuous integrably dominated process has convergent expectations
along almost surely convergent bounded measurable random times. -/
theorem Sandpile.Support.tendsto_integral_stopped_process
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (M : ℝ≥0 → Ω → ℝ) (hMm : ∀ t, StronglyMeasurable (M t))
    (hMc : ∀ ω, Continuous fun t => M t ω) (T : ℝ≥0)
    (D : Ω → ℝ) (hDi : Integrable D P)
    (hD : ∀ᵐ ω ∂P, ∀ t ≤ T, ‖M t ω‖ ≤ D ω)
    (σ : ℕ → Ω → ℝ≥0) (τ : Ω → ℝ≥0)
    (hσm : ∀ n, Measurable (σ n)) (hτm : Measurable τ)
    (hσT : ∀ n ω, σ n ω ≤ T) (hτT : ∀ ω, τ ω ≤ T)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => σ n ω) atTop (𝓝 (τ ω))) :
    Integrable (fun ω => M (τ ω) ω) P ∧
      Tendsto (fun n => ∫ ω, M (σ n ω) ω ∂P) atTop
        (𝓝 (∫ ω, M (τ ω) ω ∂P)) := by
  have hjoint : StronglyMeasurable (Function.uncurry M) :=
    stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hMc hMm
  have hm : ∀ ρ : Ω → ℝ≥0, Measurable ρ →
      AEStronglyMeasurable (fun ω => M (ρ ω) ω) P := fun ρ hρ =>
    (hjoint.comp_measurable (hρ.prodMk measurable_id)).aestronglyMeasurable
  constructor
  · exact hDi.mono' (hm τ hτm) (hD.mono fun ω hω => hω (τ ω) (hτT ω))
  · apply tendsto_integral_of_dominated_convergence D
    · exact fun n => hm (σ n) (hσm n)
    · exact hDi
    · exact fun n => hD.mono fun ω hω => hω (σ n ω) (hσT n ω)
    · filter_upwards [hlim] with ω hω
      exact ((hMc ω).tendsto (τ ω)).comp hω
