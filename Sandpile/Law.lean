/-
The mass laws used by the main theorems (`sandpile.tex`, Section 1) and the
mean odometer.
-/
import Sandpile.Basic

open MeasureTheory ProbabilityTheory

namespace Sandpile

/-- The centred field `ζ` scaled into a mass field: `σ = 1 + 2d ζ`. -/
noncomputable def centeredMassLaw (d : ℕ) (ν : Measure ℝ) : Measure (Site d → ℝ) :=
  massLaw d (ν.map fun z => 1 + 2 * (d : ℝ) * z)

instance {d : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (massLaw d μ) := by
  unfold massLaw LatticeProb.iidLaw; infer_instance

instance {d : ℕ} (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (centeredMassLaw d ν) := by
  unfold centeredMassLaw
  have : IsProbabilityMeasure (ν.map fun z => 1 + 2 * (d : ℝ) * z) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  infer_instance

/-- `E u_t(0)`, the mean odometer at the origin after `t` steps. -/
noncomputable def meanOdometer {d : ℕ} (P : Measure (Site d → ℝ)) (t : ℕ) : ℝ :=
  ∫ σ, odometer σ t 0 ∂P

end Sandpile
