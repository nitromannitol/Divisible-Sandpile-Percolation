import Sandpile.Support.Dgt4AConcTheta
import Sandpile.Support.Dgt4ACondTerminal
import Sandpile.Support.LinGaussBridge
import Sandpile.Support.Stationary

/-!
# The Green field and `\Theta_n` are everywhere measurable

The Green field is measurable in the scenery, and so is `\Theta_n`. The box limit of
`eq:dgt4-infinite-green-field` is taken with the junk value `0` where the limit does not exist,
and the set where it does exist is measurable; the field is therefore the everywhere pointwise
limit of the partial sums cut off outside that set, hence measurable, and not merely almost
everywhere measurable as the earlier modules of case (a) had it. That is what the Gaussian
concentration inequality wants of `\Theta_n`, whose Lipschitz hypothesis is a statement at every
configuration and not almost everywhere.
-/

open MeasureTheory Filter Topology

open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}

/-- The sceneries whose Green field converges at a site. -/
def greenConvAt (d : ℕ) (x : Site d) : Set (Site d → ℝ) :=
  {ζ | ∃ L : ℝ, Tendsto (fun n => infiniteGreenFieldPartial n ζ x) atTop (𝓝 L)}

/-- The set of sceneries at which the Green field converges at `x` is measurable, since it is
built from the measurable partial sums via `measurableSet_exists_tendsto`. -/
theorem measurableSet_greenConvAt (x : Site d) : MeasurableSet (greenConvAt d x) :=
  MeasureTheory.measurableSet_exists_tendsto
    (fun n => measurable_infiniteGreenFieldPartial n x)

/-- Outside `greenConvAt`, the Green field takes the junk value `0` by definition. -/
theorem infiniteGreenField_of_notMem {ζ : Site d → ℝ} {x : Site d}
    (h : ζ ∉ greenConvAt d x) : infiniteGreenField ζ x = 0 := by
  rw [infiniteGreenField]
  exact dif_neg h

/-- **The Green field is measurable in the scenery.** -/
theorem measurable_infiniteGreenField (x : Site d) :
    Measurable (fun ζ : Site d → ℝ => infiniteGreenField ζ x) := by
  refine measurable_of_tendsto_metrizable
    (f := fun n => (greenConvAt d x).indicator
      (fun ζ : Site d → ℝ => infiniteGreenFieldPartial n ζ x))
    (fun n => (measurable_infiniteGreenFieldPartial n x).indicator
      (measurableSet_greenConvAt x)) ?_
  refine tendsto_pi_nhds.2 fun ζ => ?_
  by_cases hζ : ζ ∈ greenConvAt d x
  · refine (tendsto_infiniteGreenFieldPartial hζ).congr fun n => ?_
    rw [Set.indicator_of_mem hζ]
  · rw [infiniteGreenField_of_notMem hζ]
    refine tendsto_const_nhds.congr fun n => ?_
    rw [Set.indicator_of_notMem hζ]

/-- **`\Theta_n` is measurable in the residual.** -/
theorem measurable_condTheta (hd : 5 ≤ d) (c s a : ℝ) (t j : ℕ) :
    Measurable (condTheta d hd c s a t j) := by
  have hrw : condTheta d hd c s a t j
      = fun r : Site d → ℝ => ∑ z ∈ boxFinset (0 : Site d) j, heatKernel d j 0 z *
        (infiniteGreenField (condScenery d hd c r s) z
          - odometerOf (condScenery d hd c r s) t z + a) := by
    funext r
    exact avg_iterate_eq_finsetSum _ _ _
  rw [hrw]
  refine Finset.measurable_sum _ fun z _ => ?_
  refine Measurable.const_mul ?_ _
  refine Measurable.add ?_ measurable_const
  exact ((measurable_infiniteGreenField z).comp (measurable_condScenery hd c s)).sub
    ((measurable_odometerOf t z).comp (measurable_condScenery hd c s))

end Sandpile
