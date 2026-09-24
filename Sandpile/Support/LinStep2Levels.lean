/-
The monotonicity of the levels of Step 2 of `lem:dgt4-path-survival`.

The reduction of the threshold intersection to the last visits
(`Sandpile.iInter_lastVisit_eq`) needs the levels `b_r=\E u_{n-r-1}(0)` to be ANTITONE in the
time index, which is the paper's "monotonicity of $\E u_m(0)$" at `sandpile.tex:5551`.  That
monotonicity is the pathwise monotonicity of the odometer in the number of relaxation steps
(`Sandpile.odometer_mono`) integrated against the scenery law, which is
`Sandpile.meanOdometer_mono` of `Support/HeightLower.lean`.  What is added here is only the
reindexing `r \mapsto n-r-1`, since the paper's level at time `r` is the mean odometer at time
`n_R-r-1` and the reduction to last visits asks for an antitone function of `r`.
-/
import Sandpile.Support.HeightLower

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile

variable {d : ℕ}

/-- The paper's levels `b_r = E u_{n-r-1}(0)` are antitone in `r`, which is what the reduction
to last visits needs. -/
theorem antitone_level (ν : Measure ℝ) [IsProbabilityMeasure ν] (n : ℕ)
    (hmono : Monotone (fun t : ℕ => meanOdometer (centeredMassLaw d ν) t)) :
    Antitone (fun r : ℕ => meanOdometer (centeredMassLaw d ν) (n - r - 1)) := by
  intro r s hrs
  exact hmono (by omega)

end Sandpile
