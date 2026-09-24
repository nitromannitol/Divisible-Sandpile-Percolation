/-
The integral form of the pointwise bound on the centred deviation `D_n` of
`sandpile.tex:5050-5055`: integrating `|D_n|\leq I+E`, where `I` is the odometer increment at
the origin and `E` the positive part of the excess of the averaged field over the field, gives
the same bound for the expectations.  It is the first half of the first-moment bound
`E|D_n|\leq2E u_n(0)/n`.
-/
import Sandpile.Support.Dgt4ADeviationAbs

open MeasureTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

/-- `E|D_n|\leq E I+E E` (`sandpile.tex:5049-5050`). -/
theorem integral_abs_centeredDeviation_le_add {μ : Measure (Site d → ℝ)} (n : ℕ)
    (hpt : ∀ ζ : Site d → ℝ,
      |centeredDeviation d ζ n|
        ≤ (odometerOf ζ (n + 1) 0 - odometerOf ζ n 0)
          + max 0 (avg (fun y => infiniteGreenField ζ y - odometerOf ζ n y) 0
              - infiniteGreenField ζ 0))
    (hint1 : Integrable (fun ζ : Site d → ℝ => |centeredDeviation d ζ n|) μ)
    (hint2 : Integrable (fun ζ : Site d → ℝ => odometerOf ζ (n + 1) 0 - odometerOf ζ n 0) μ)
    (hint3 : Integrable (fun ζ : Site d → ℝ =>
      max 0 (avg (fun y => infiniteGreenField ζ y - odometerOf ζ n y) 0
        - infiniteGreenField ζ 0)) μ) :
    (∫ ζ : Site d → ℝ, |centeredDeviation d ζ n| ∂μ)
      ≤ (∫ ζ : Site d → ℝ, (odometerOf ζ (n + 1) 0 - odometerOf ζ n 0) ∂μ)
        + ∫ ζ : Site d → ℝ, max 0 (avg (fun y => infiniteGreenField ζ y - odometerOf ζ n y) 0
            - infiniteGreenField ζ 0) ∂μ := by
  have h := integral_mono_ae hint1 (hint2.add hint3) (Filter.Eventually.of_forall hpt)
  simp only [Pi.add_apply] at h
  rw [integral_add hint2 hint3] at h
  exact h

end Sandpile
