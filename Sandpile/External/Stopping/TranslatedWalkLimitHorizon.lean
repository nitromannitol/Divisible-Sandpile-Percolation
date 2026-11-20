import Sandpile.External.Stopping.TranslatedWalkLimitReward
import Sandpile.External.Stopping.ClockHorizonWeakLimit

/-!
# Cube rewards of varying-horizon walk limits

A horizon bound for a weak limit follows from converging bounds on the
approximating walk clocks.
-/

open MeasureTheory ProbabilityTheory Set Filter unitInterval Topology
open scoped NNReal ENNReal ProbabilityTheory

namespace Sandpile.External.Stopping

/-- Weak limits of killed walk-clock laws with converging horizon bounds have
reward at most the corresponding Brownian cube value. -/
theorem integral_walk_clock_limit_le_translated_cube_of_tendsto_horizon
    {d : ℕ} [NeZero d] {ι : Type*} [Countable ι]
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n) (hR : Tendsto R atTop atTop)
    (q : ℕ → Site d) (a : Continuum.Space d)
    (hstart : Tendsto (fun n => Lclt.scaledSite (R n) (q n)) atTop (𝓝 a))
    (τ : ℕ → (ℕ → Site d) → ℕ) (hτ : ∀ n, IsWalkStopping (τ n))
    (hτm : ∀ n, Measurable (τ n))
    (hkill : ∀ n, ∀ᵐ X ∂(walkLaw d (q n)), ∀ j < τ n X, X j ∈ supBox (q n) (R n))
    (θ : ℕ → (ℕ → Site d) → I) (hθ : ∀ n, Measurable (θ n))
    (c : ℝ≥0) (hc : 0 < c)
    (hdecode : ∀ n X, c * unitClock id (θ n X) = diffusiveLatticeClock (R n) (τ n X))
    (μn : ℕ → ProbabilityMeasure (C(ℝ≥0, Continuum.Space d) × I))
    (μ : ProbabilityMeasure (C(ℝ≥0, Continuum.Space d) × I))
    (hμn : ∀ n, (μn n : Measure _) = (walkLaw d (q n)).map
      (fun X => (diffusiveWalkPath (R n) X, θ n X)))
    (hμ : Tendsto μn atTop (𝓝 μ)) (H : ℕ → ℝ≥0) (T : ℝ≥0)
    (hH : Tendsto H atTop (𝓝 T))
    (hbound : ∀ n, ∀ᵐ p ∂(μn n : Measure (C(ℝ≥0, Continuum.Space d) × I)),
      c * unitClock id p.2 ≤ H n)
    (hB : Continuum.IsBrownian d a (fun t (f : C(ℝ≥0, Continuum.Space d)) => f t)
      (μ : Measure (C(ℝ≥0, Continuum.Space d) × I)).fst)
    (time : ι → ℝ≥0) (hdense : ∀ u v : ℝ≥0, u < v → ∃ i, u < time i ∧ time i < v)
    (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ t z, |G t z| ≤ M) :
    (∫ p, G ((T : ℝ) - ((c * unitClock id p.2 : ℝ≥0) : ℝ))
      (p.1 (c * unitClock id p.2)) ∂(μ : Measure (C(ℝ≥0, Continuum.Space d) × I))) ≤
      Continuum.brownianDiscountCube (fun t (f : C(ℝ≥0, Continuum.Space d)) => f t)
        (μ : Measure (C(ℝ≥0, Continuum.Space d) × I)).fst (fun s z => -G s z) T 1 a := by
  have hclock : Continuous (fun z : I => c * unitClock id z) :=
    continuous_const.mul continuous_unitClock
  have hclockT := ae_clock_le_of_tendsto_probabilityMeasure μn μ hμ
    (fun z => c * unitClock id z) hclock H T hH hbound
  exact integral_walk_clock_limit_le_translated_brownian_cube R hRpos hR q a hstart τ hτ hτm
    hkill θ hθ c hc hdecode μn μ hμn hμ T hclockT hB time hdense G hGc M hG

end Sandpile.External.Stopping
