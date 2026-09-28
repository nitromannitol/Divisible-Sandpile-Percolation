import Sandpile.Basic

/-!
# Mass laws and the mean odometer

This file defines the i.i.d. mass laws used by the main theorems of `sandpile.tex` Section 1 and
the mean odometer they induce. `centeredMassLaw d ν` is the law of the mass field
`σ = 1 + 2d ζ` for scenery `ζ` of law `ν`, and `meanOdometer` is the expected odometer at the
origin after `t` steps under a given mass law. Both `massLaw` and `centeredMassLaw` are shown to
be probability measures whenever their scenery law is.
-/

open MeasureTheory ProbabilityTheory

namespace Sandpile

/-- The centred field `ζ` scaled into a mass field: `σ = 1 + 2d ζ`. -/
noncomputable def centeredMassLaw (d : ℕ) (ν : Measure ℝ) : Measure (Site d → ℝ) :=
  massLaw d (ν.map fun z => 1 + 2 * (d : ℝ) * z)

/-- `massLaw d μ`, the i.i.d. law of a mass field with one-site law `μ`, is a probability measure
whenever `μ` is. -/
instance {d : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (massLaw d μ) := by
  unfold massLaw LatticeProb.iidLaw; infer_instance

/-- `centeredMassLaw d ν` is a probability measure whenever the scenery law `ν` is, since it is
the pushforward of `massLaw d` along an affine map of a probability measure. -/
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
