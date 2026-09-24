/-
The first-moment bound of case (a) Step 1 of `prop:dgt4-contact-asymptotics`
(`sandpile.tex:5053-5055`): `E|D_n| ≤ 2 E u_n(0)/n`.  It combines the pointwise
bound `E|D_n| ≤ 2E(u_{n+1}(0)-u_n(0))` with the identification of that increment
with the increment of the mean odometer and the concavity bound
`eq:dgt4-mean-increment-bound`.
-/
import Sandpile.Support.Dgt4AFirstMomentTwo
import Sandpile.Support.Dgt4AMeanIncrementInt
import Sandpile.Support.Dgt4AMeanIncrement

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

/-- `E|D_n| ≤ 2 E u_n(0)/n` (`sandpile.tex:5048-5050`). -/
theorem integral_abs_centeredDeviation_le_two_mean_div (hd : 1 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hintν : Integrable id ν) (hmeanν : ∫ w, w ∂ν = 0)
    (hposν : Integrable (fun z : ℝ => max z 0) ν)
    (n : ℕ) (hn : 1 ≤ n)
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
      (∫ ζ : Site d → ℝ, (infiniteGreenField ζ y - odometerOf ζ n y)
          ∂(LatticeProb.iidLaw d ν))
        = ∫ ζ : Site d → ℝ, (infiniteGreenField ζ 0 - odometerOf ζ n 0)
            ∂(LatticeProb.iidLaw d ν))
    (hint1 : Integrable (fun ζ : Site d → ℝ => |centeredDeviation d ζ n|)
      (LatticeProb.iidLaw d ν))
    (hint2 : Integrable (fun ζ : Site d → ℝ =>
      odometerOf ζ (n + 1) 0 - odometerOf ζ n 0) (LatticeProb.iidLaw d ν))
    (hint3 : Integrable (fun ζ : Site d → ℝ =>
      max 0 (avg (fun y => infiniteGreenField ζ y - odometerOf ζ n y) 0
        - infiniteGreenField ζ 0)) (LatticeProb.iidLaw d ν))
    (hint4 : Integrable (fun ζ : Site d → ℝ =>
      infiniteGreenField ζ 0 - odometerOf ζ n 0) (LatticeProb.iidLaw d ν))
    (hint5 : ∀ y : Site d,
      Integrable (fun ζ : Site d → ℝ =>
        infiniteGreenField ζ y - odometerOf ζ n y) (LatticeProb.iidLaw d ν))
    (hint6 : Integrable (fun ζ : Site d → ℝ =>
      avg (fun y => infiniteGreenField ζ y - odometerOf ζ n y) 0)
        (LatticeProb.iidLaw d ν)) :
    (∫ ζ : Site d → ℝ, |centeredDeviation d ζ n| ∂(LatticeProb.iidLaw d ν))
      ≤ 2 * meanOdometer (centeredMassLaw d ν) n / n := by
  have h1 := integral_abs_centeredDeviation_le_two_increment (d := d) (μ := LatticeProb.iidLaw d ν)
    hd n hpt hsplit hstat hint1 hint2 hint3 hint4 hint5 hint6
  have h2 := integral_odometerOf_increment (d := d) hd ν hposν n
  have h3 := meanOdometer_increment_le_div (d := d) hd ν hintν hmeanν hposν n hn
  rw [h2] at h1
  have h4 : 2 * (meanOdometer (centeredMassLaw d ν) (n + 1)
      - meanOdometer (centeredMassLaw d ν) n)
      ≤ 2 * (meanOdometer (centeredMassLaw d ν) n / n) := by linarith
  have h5 : 2 * meanOdometer (centeredMassLaw d ν) n / n
      = 2 * (meanOdometer (centeredMassLaw d ν) n / n) := by ring
  rw [h5]
  linarith

end Sandpile
