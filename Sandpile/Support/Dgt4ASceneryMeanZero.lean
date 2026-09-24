/-
`\E D_n=0` (`sandpile.tex:5055`), read off the finite-coordinate form
`D_n=\zeta(0)-(u_n(0)-Pu_n(0))`: the scenery is centred and the mean odometer does not
depend on the site, so the neighbour average has the same mean as the odometer itself.
-/
import Sandpile.Support.Dgt4ADeviationScenery
import Sandpile.Support.Dgt4AAvgIntegral
import Sandpile.Support.IncrementBall
import Sandpile.Support.BlockIncrement

open MeasureTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

/-- `\E D_n=0` (`sandpile.tex:5050`). -/
theorem integral_sceneryDeviation_eq_zero (hd : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) (hmean : ∫ z, z ∂ν = 0)
    (hpos : Integrable (fun z : ℝ => max z 0) ν) (n : ℕ) :
    (∫ ζ, sceneryDeviation d ζ n ∂(LatticeProb.iidLaw d ν)) = 0 := by
  have hI1 : Integrable (fun ζ : Site d → ℝ => ζ (0 : Site d)) (LatticeProb.iidLaw d ν) :=
    Sandpile.integrable_coord ν hint 0
  have hI2 : Integrable (fun ζ : Site d → ℝ => Sandpile.odometerOf ζ n 0)
      (LatticeProb.iidLaw d ν) := Sandpile.integrable_odometerOf d ν hpos n 0
  have hI3 : Integrable (fun ζ : Site d → ℝ =>
      Sandpile.avg (fun y => Sandpile.odometerOf ζ n y) (0 : Site d))
      (LatticeProb.iidLaw d ν) := by
    have h := Sandpile.integrable_avg_iterate_odometerOf (d := d) ν hpos 1 n 0
    simpa using h
  have havg : (∫ ζ, Sandpile.avg (fun y => Sandpile.odometerOf ζ n y) (0 : Site d)
        ∂(LatticeProb.iidLaw d ν))
      = ∫ ζ, Sandpile.odometerOf ζ n 0 ∂(LatticeProb.iidLaw d ν) :=
    Sandpile.integral_avg_eq_of_site_invariant hd (fun ζ y => Sandpile.odometerOf ζ n y)
      (fun y => Sandpile.integrable_odometerOf d ν hpos n y)
      (fun y => Sandpile.integral_odometerOf_eq d ν n y)
  have hI23 : Integrable (fun ζ : Site d → ℝ => Sandpile.odometerOf ζ n 0
      - Sandpile.avg (fun y => Sandpile.odometerOf ζ n y) (0 : Site d))
      (LatticeProb.iidLaw d ν) := hI2.sub hI3
  show (∫ ζ : Site d → ℝ, (ζ 0 - (Sandpile.odometerOf ζ n 0
      - Sandpile.avg (fun y => Sandpile.odometerOf ζ n y) 0)) ∂(LatticeProb.iidLaw d ν)) = 0
  rw [integral_sub hI1 hI23, integral_sub hI2 hI3, havg,
    Sandpile.integral_coord ν hint 0, hmean]
  ring


end Sandpile
