import Sandpile.Support.Dgt4ADeviationAbs
import Sandpile.Support.Dgt4AAvgIntegral

/-!
# The centred deviation has mean zero

The centred deviation `D_n` of `sandpile.tex:5050-5051` has mean zero: "by stationarity,
`D_n` has mean zero" (`sandpile.tex:5055`). The neighbour average `P` of a function whose
expectation is the same at every site has the same expectation as the function itself, so
`E P(V_∞-u_n)(0) = E(V_∞-u_n)(0)` and the two terms of `D_n` cancel.
-/

open MeasureTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

/-- `E D_n=0` (`sandpile.tex:5050`). -/
theorem integral_centeredDeviation_eq_zero {μ : Measure (Site d → ℝ)} (hd : 1 ≤ d) (n : ℕ)
    (hstat : ∀ y : Site d,
      (∫ ζ : Site d → ℝ, (infiniteGreenField ζ y - odometerOf ζ n y) ∂μ)
        = ∫ ζ : Site d → ℝ, (infiniteGreenField ζ 0 - odometerOf ζ n 0) ∂μ)
    (hint1 : Integrable (fun ζ : Site d → ℝ => infiniteGreenField ζ 0 - odometerOf ζ n 0) μ)
    (hint2 : ∀ y : Site d,
      Integrable (fun ζ : Site d → ℝ => infiniteGreenField ζ y - odometerOf ζ n y) μ)
    (hint3 : Integrable (fun ζ : Site d → ℝ =>
      avg (fun y => infiniteGreenField ζ y - odometerOf ζ n y) 0) μ) :
    (∫ ζ : Site d → ℝ, centeredDeviation d ζ n ∂μ) = 0 := by
  have hsplit : (∫ ζ : Site d → ℝ, centeredDeviation d ζ n ∂μ)
      = (∫ ζ : Site d → ℝ, (infiniteGreenField ζ 0 - odometerOf ζ n 0) ∂μ)
        - ∫ ζ : Site d → ℝ, avg (fun y => infiniteGreenField ζ y - odometerOf ζ n y) 0 ∂μ := by
    simp only [centeredDeviation]
    rw [integral_sub hint1 hint3]
  rw [hsplit, Sandpile.integral_avg_eq_of_site_invariant hd _ hint2 hstat]
  ring

end Sandpile
