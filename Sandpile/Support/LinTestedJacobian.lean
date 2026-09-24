/-
`eq:odometer-derivative` for the tested field.

The convex-linear bound is driven by the right derivative that convexity
supplies; the paper's Step 1 computes instead the Jacobian
`∂_{ζ(z)}u_{n}(x) = odometerJacobian`.  Off the null set where the odometer
recursion is degenerate the two agree, so the derivative variances and mean
gradients of Step 1 are exactly the ones Step 2 consumes.
-/
import Sandpile.Support.LinTestedField
import Sandpile.Support.OdometerJacobian

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile

variable {d : ℕ}

/-- **The right derivative of the tested field is its Jacobian, almost surely.**
`eq:odometer-derivative` holds off the null set where the odometer recursion is
degenerate, so the paper's `∂_{ζ(z)}F_R` and the right derivative supplied by
convexity agree for almost every scenery. -/
theorem rightDerivField_testedField_ae (ν : Measure ℝ) [IsProbabilityMeasure ν]
    [NullSingletonClass ν] (s : Finset (Site d)) (a : Site d → ℝ) (n : ℕ) (v : Site d) :
    ∀ᵐ ζ ∂(LatticeProb.iidLaw d ν),
      rightDerivField (testedField s a n) v ζ
        = ∑ x ∈ s, a x * odometerJacobian ζ n x v := by
  filter_upwards [Sandpile.ae_odometer_preactivation_ne_zero (d := d) ν] with ζ hζ
  have hD : HasDerivAt (fun y => testedField s a n (Function.update ζ v y))
      (∑ x ∈ s, a x * odometerJacobian ζ n x v) (ζ v) := by
    have hterm : ∀ x ∈ s, HasDerivAt
        (fun y => a x * odometerOf (Function.update ζ v y) n x)
        (a x * odometerJacobian ζ n x v) (ζ v) :=
      fun x _ => ((Sandpile.hasDerivAt_odometerOf ζ hζ n x v).const_mul (a x))
    exact HasDerivAt.fun_sum hterm
  have := (hD.hasDerivWithinAt (s := Set.Ioi (ζ v))).derivWithin (uniqueDiffWithinAt_Ioi _)
  simpa [rightDerivField] using this

/-- The mean gradient of the tested field is the mean of its Jacobian. -/
theorem integral_rightDerivField_testedField (ν : Measure ℝ) [IsProbabilityMeasure ν]
    [NullSingletonClass ν] (s : Finset (Site d)) (a : Site d → ℝ) (n : ℕ) (v : Site d) :
    ∫ ζ, rightDerivField (testedField s a n) v ζ ∂(LatticeProb.iidLaw d ν)
      = ∫ ζ, (∑ x ∈ s, a x * odometerJacobian ζ n x v) ∂(LatticeProb.iidLaw d ν) :=
  integral_congr_ae (rightDerivField_testedField_ae ν s a n v)

/-- The derivative variance of the tested field is the variance of its Jacobian. -/
theorem variance_rightDerivField_testedField (ν : Measure ℝ) [IsProbabilityMeasure ν]
    [NullSingletonClass ν] (s : Finset (Site d)) (a : Site d → ℝ) (n : ℕ) (v : Site d) :
    variance (rightDerivField (testedField s a n) v) (LatticeProb.iidLaw d ν)
      = variance (fun ζ => ∑ x ∈ s, a x * odometerJacobian ζ n x v)
          (LatticeProb.iidLaw d ν) :=
  variance_congr (rightDerivField_testedField_ae ν s a n v)

end Sandpile
