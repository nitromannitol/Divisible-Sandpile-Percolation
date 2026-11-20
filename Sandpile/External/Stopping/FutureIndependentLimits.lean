import Sandpile.External.Stopping.FutureIncrementPath
import Sandpile.External.Stopping.IndependentAlmostSureLimits

/-!
# Closing a gap between past and future

Independence from future increments at times converging to `t` implies
independence from increments after `t`. This removes a positive time gap in
the stopping-time weak-limit argument.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace Sandpile.External.Stopping

/-- If observations are independent of future-increment paths at a sequence
of times converging to `t`, they are independent of the future at `t`. -/
theorem indepFun_futureIncrementPath_of_tendsto {d : ℕ} {Ω E : Type*}
    [MeasurableSpace Ω] [MetricSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Ω → C(ℝ≥0, Continuum.Space d)) (Y : Ω → E)
    (hW : Measurable W) (hY : Measurable Y)
    (u : ℕ → ℝ≥0) (t : ℝ≥0) (hu : Tendsto u atTop (𝓝 t))
    (hind : ∀ n, IndepFun (fun ω => futureIncrementPath (u n) (W ω)) Y P) :
    IndepFun (fun ω => futureIncrementPath t (W ω)) Y P := by
  letI : MetricSpace C(ℝ≥0, Continuum.Space d) :=
    TopologicalSpace.metrizableSpaceMetric _
  apply indepFun_of_ae_tendsto P
    (fun n ω => futureIncrementPath (u n) (W ω)) (fun _ => Y)
    (fun ω => futureIncrementPath t (W ω)) Y
  · intro n
    exact (continuous_futureIncrementPath (u n)).measurable.comp hW
  · exact fun _ => hY
  · exact (continuous_futureIncrementPath t).measurable.comp hW
  · exact hY
  · filter_upwards [] with ω
    have h := (continuous_futureIncrementPath_uncurry.tendsto (t, W ω)).comp
      (hu.prodMk_nhds tendsto_const_nhds)
    exact h.prodMk_nhds tendsto_const_nhds
  · exact hind

end Sandpile.External.Stopping
