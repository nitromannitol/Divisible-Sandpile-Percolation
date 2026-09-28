import Sandpile.Support.Dgt4ADeviationAbs

/-!
# The excess term's mean, in terms of `D_n` and the increment

The excess term of the split of the centred deviation `D_n` of `sandpile.tex:5050-5055` has
expectation equal to the expectation of the odometer increment minus the mean of `D_n`:
`E E = E I - E D_n`. With the mean-zero property of `D_n` this identifies the two terms of
`E|D_n|\leq E I+E E`, which is what makes the first-moment bound `2E u_n(0)/n` sharp.
-/

open MeasureTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

/-- `E E=E I-E D_n` (`sandpile.tex:5049-5050`). -/
theorem integral_excess_eq_increment_sub {μ : Measure (Site d → ℝ)} (n : ℕ)
    (hpt : ∀ ζ : Site d → ℝ,
      centeredDeviation d ζ n
        = (odometerOf ζ (n + 1) 0 - odometerOf ζ n 0)
          - max 0 (avg (fun y => infiniteGreenField ζ y - odometerOf ζ n y) 0
              - infiniteGreenField ζ 0))
    (hint1 : Integrable (fun ζ : Site d → ℝ => odometerOf ζ (n + 1) 0 - odometerOf ζ n 0) μ)
    (hint2 : Integrable (fun ζ : Site d → ℝ =>
      max 0 (avg (fun y => infiniteGreenField ζ y - odometerOf ζ n y) 0
        - infiniteGreenField ζ 0)) μ) :
    (∫ ζ : Site d → ℝ, max 0 (avg (fun y => infiniteGreenField ζ y - odometerOf ζ n y) 0
        - infiniteGreenField ζ 0) ∂μ)
      = (∫ ζ : Site d → ℝ, (odometerOf ζ (n + 1) 0 - odometerOf ζ n 0) ∂μ)
        - ∫ ζ : Site d → ℝ, centeredDeviation d ζ n ∂μ := by
  have h := integral_sub hint1 hint2
  have h2 : (∫ ζ : Site d → ℝ, (odometerOf ζ (n + 1) 0 - odometerOf ζ n 0
      - max 0 (avg (fun y => infiniteGreenField ζ y - odometerOf ζ n y) 0
          - infiniteGreenField ζ 0)) ∂μ) = ∫ ζ : Site d → ℝ, centeredDeviation d ζ n ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun ζ => (hpt ζ).symm)
  linarith [h, h2]

end Sandpile
