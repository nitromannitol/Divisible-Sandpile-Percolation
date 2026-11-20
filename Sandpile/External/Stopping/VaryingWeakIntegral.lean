import Sandpile.External.Stopping.WalkClockCompactness
import Mathlib.MeasureTheory.Measure.DiracProba

/-!
# Jointly continuous rewards under weak convergence

When a deterministic parameter converges and probability laws converge
weakly, bounded continuous rewards depending jointly on the parameter and the
random variable have convergent expectations.
-/

open MeasureTheory Filter Topology TopologicalSpace
open scoped BoundedContinuousFunction

namespace Sandpile.External.Stopping

/-- A converging deterministic parameter can be included in a weakly
convergent probability law. -/
theorem tendsto_integral_boundedContinuous_of_parameter
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [PseudoMetrizableSpace E]
    (μ : ℕ → ProbabilityMeasure E) (ν : ProbabilityMeasure E)
    (hμ : Tendsto μ atTop (𝓝 ν)) (a : ℕ → ℝ) (b : ℝ)
    (ha : Tendsto a atTop (𝓝 b)) (F : (ℝ × E) →ᵇ ℝ) :
    Tendsto (fun n => ∫ x, F (a n, x) ∂(μ n : Measure E)) atTop
      (𝓝 (∫ x, F (b, x) ∂(ν : Measure E))) := by
  have hdirac : Tendsto (fun n => diracProba (a n)) atTop (𝓝 (diracProba b)) :=
    (continuous_diracProba.tendsto b).comp ha
  have hprod := (ProbabilityMeasure.continuous_prod.tendsto (diracProba b, ν)).comp
    (hdirac.prodMk_nhds hμ)
  have h := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hprod) F
  have heq (r : ℝ) (P : ProbabilityMeasure E) :
      ∫ z, F z ∂((diracProba r).prod P : Measure (ℝ × E)) =
        ∫ x, F (r, x) ∂(P : Measure E) := by
    change ∫ z, F z ∂(Measure.dirac r).prod (P : Measure E) = _
    rw [Measure.dirac_prod, integral_map measurable_prodMk_left.aemeasurable
      F.continuous.measurable.aestronglyMeasurable]
  simpa only [Function.comp_apply, heq] using h

end Sandpile.External.Stopping
