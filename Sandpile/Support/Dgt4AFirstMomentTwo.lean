/-
The first-moment bound for the centred deviation `D_n` of `sandpile.tex:5050-5055`:
`E|D_n| ≤ 2E(u_{n+1}(0)-u_n(0))`.  The pointwise bound `|D_n| ≤ I+E`, the identity
`E E = E I - E D_n` and the mean-zero property `E D_n = 0` give `E|D_n| ≤ E I + E I`.
-/
import Sandpile.Support.Dgt4ADeviationAbs
import Sandpile.Support.Dgt4AFirstMomentAdd
import Sandpile.Support.Dgt4AFirstMomentExcess
import Sandpile.Support.Dgt4AMeanZero

open MeasureTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

theorem integral_abs_centeredDeviation_le_two_increment {μ : Measure (Site d → ℝ)} (hd : 1 ≤ d)
    (n : ℕ)
    (hpt : ∀ ζ : Site d → ℝ,
      |centeredDeviation d ζ n|
        ≤ (odometerOf ζ (n + 1) 0 - odometerOf ζ n 0)
          + max 0 (avg (fun y => infiniteGreenField ζ y - odometerOf ζ n y) 0
              - infiniteGreenField ζ 0))
    (hsplit : ∀ ζ : Site d → ℝ,
      centeredDeviation d ζ n
        = (odometerOf ζ (n + 1) 0 - odometerOf ζ n 0)
          - max 0 (avg (fun y => infiniteGreenField ζ y - odometerOf ζ n y) 0
              - infiniteGreenField ζ 0))
    (hstat : ∀ y : Site d,
      (∫ ζ : Site d → ℝ, (infiniteGreenField ζ y - odometerOf ζ n y) ∂μ)
        = ∫ ζ : Site d → ℝ, (infiniteGreenField ζ 0 - odometerOf ζ n 0) ∂μ)
    (hint1 : Integrable (fun ζ : Site d → ℝ => |centeredDeviation d ζ n|) μ)
    (hint2 : Integrable (fun ζ : Site d → ℝ => odometerOf ζ (n + 1) 0 - odometerOf ζ n 0) μ)
    (hint3 : Integrable (fun ζ : Site d → ℝ =>
      max 0 (avg (fun y => infiniteGreenField ζ y - odometerOf ζ n y) 0
        - infiniteGreenField ζ 0)) μ)
    (hint4 : Integrable (fun ζ : Site d → ℝ => infiniteGreenField ζ 0 - odometerOf ζ n 0) μ)
    (hint5 : ∀ y : Site d,
      Integrable (fun ζ : Site d → ℝ => infiniteGreenField ζ y - odometerOf ζ n y) μ)
    (hint6 : Integrable (fun ζ : Site d → ℝ =>
      avg (fun y => infiniteGreenField ζ y - odometerOf ζ n y) 0) μ) :
    (∫ ζ : Site d → ℝ, |centeredDeviation d ζ n| ∂μ)
      ≤ 2 * ∫ ζ : Site d → ℝ, (odometerOf ζ (n + 1) 0 - odometerOf ζ n 0) ∂μ := by
  have h1 := integral_abs_centeredDeviation_le_add n hpt hint1 hint2 hint3
  have h2 := integral_excess_eq_increment_sub n hsplit hint2 hint3
  have h3 := integral_centeredDeviation_eq_zero hd n hstat hint4 hint5 hint6
  have h4 : (∫ ζ : Site d → ℝ, max 0 (avg (fun y => infiniteGreenField ζ y - odometerOf ζ n y) 0
      - infiniteGreenField ζ 0) ∂μ)
      = ∫ ζ : Site d → ℝ, (odometerOf ζ (n + 1) 0 - odometerOf ζ n 0) ∂μ := by
    rw [h2, h3]; ring
  linarith

end Sandpile
