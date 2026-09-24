/-
The mean-increment bound `eq:dgt4-mean-increment-bound` (`sandpile.tex:4118-4121`):
`0 ≤ E u_{t+1}(0) - E u_t(0) ≤ E u_t(0)/t`.  The upper bound is the concavity of
the mean odometer: the increments are nonincreasing, so `t` times the last
increment is at most the total.
-/
import Sandpile.Support.HeightLower

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile

variable {d : ℕ}

/-- `eq:dgt4-mean-increment-bound` (`sandpile.tex:4113-4116`): the mean increment is at
most the mean divided by the time. -/
theorem meanOdometer_increment_le_div (hd : 1 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) (hmean : ∫ w, w ∂ν = 0)
    (hpos : Integrable (fun z => max z 0) ν) (t : ℕ) (ht : 1 ≤ t) :
    meanOdometer (centeredMassLaw d ν) (t + 1) - meanOdometer (centeredMassLaw d ν) t
      ≤ meanOdometer (centeredMassLaw d ν) t / t := by
  have hstep := Sandpile.concave_seq_step (fun n => Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n)
    (Sandpile.meanOdometer_zero d ν) (fun k => Sandpile.meanOdometer_concave hd ν hint hmean hpos k) t
  have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  rw [le_div_iff₀ htR]
  nlinarith [hstep]

end Sandpile
