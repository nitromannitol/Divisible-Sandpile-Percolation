/-
The expectation of the odometer increment at the origin is the increment of the mean
odometer: the bridge `meanOdometer_eq` of `Support/SceneryBridge.lean` identifies the mean
odometer with the integral of `odometerOf` under the i.i.d. scenery law, and the integral of
a difference is the difference of the integrals.
-/
import Sandpile.Support.SceneryBridge
import Sandpile.Support.BlockIncrement

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile

variable {d : ℕ}

/-- `E(u_{n+1}(0)-u_n(0)) = E u_{n+1}(0) - E u_n(0)` (`sandpile.tex:4113-4116`). -/
theorem integral_odometerOf_increment (hd : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hpos : Integrable (fun z : ℝ => max z 0) ν) (n : ℕ) :
    (∫ ζ : Site d → ℝ, (odometerOf ζ (n + 1) 0 - odometerOf ζ n 0)
        ∂(LatticeProb.iidLaw d ν))
      = meanOdometer (centeredMassLaw d ν) (n + 1) - meanOdometer (centeredMassLaw d ν) n := by
  rw [integral_sub (Sandpile.integrable_odometerOf d ν hpos (n + 1) 0)
    (Sandpile.integrable_odometerOf d ν hpos n 0)]
  rw [← Sandpile.meanOdometer_eq d ν hd (n + 1), ← Sandpile.meanOdometer_eq d ν hd n]

end Sandpile
