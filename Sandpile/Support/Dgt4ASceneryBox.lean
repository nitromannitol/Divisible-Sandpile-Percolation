import Sandpile.Support.Dgt4ADeviationScenery
import Sandpile.Support.FiniteCoord
import Sandpile.Support.Stationary
import Sandpile.Support.Kernel

/-!
# `D_n` depends on the scenery only through a finite box

The finite-coordinate form of `D_n` reads only the box `Q(0,n+1)`: the odometer at `x` after `n`
steps reads the box of radius `n` about `x`, and the neighbour average at the origin reads those
boxes about the `2d` neighbours.
-/

open MeasureTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

/-- `D_n` depends on the scenery only through the box `Q(0,n+1)`. -/
theorem sceneryDeviation_congr_box (n : ℕ) (ζ η : Site d → ℝ)
    (he : ∀ z ∈ boxFinset (0 : Site d) (n + 1), ζ z = η z) :
    sceneryDeviation d ζ n = sceneryDeviation d η n := by
  have hnbr : ∀ x : Site d, Sandpile.boxDist 0 x ≤ 1 →
      Sandpile.odometerOf ζ n x = Sandpile.odometerOf η n x := by
    intro x hx
    refine Sandpile.odometerOf_congr_box n x ζ η fun z hz => he z ?_
    have h := Sandpile.boxDist_trans (0 : Site d) x z
    exact Sandpile.mem_boxFinset (by omega)
  have h0 : ζ 0 = η 0 := he 0 (Sandpile.mem_boxFinset (by simp [Sandpile.boxDist_self]))
  have hu : Sandpile.odometerOf ζ n 0 = Sandpile.odometerOf η n 0 :=
    hnbr 0 (by simp [Sandpile.boxDist_self])
  have havg : Sandpile.avg (fun y => Sandpile.odometerOf ζ n y) 0
      = Sandpile.avg (fun y => Sandpile.odometerOf η n y) 0 := by
    unfold Sandpile.avg LatticeProb.walkOp LatticeProb.nbrSum
    congr 1
    exact Finset.sum_congr rfl fun i _ => congrArg₂ (· + ·)
      (hnbr _ (Sandpile.boxDist_add_unit 0 i)) (hnbr _ (Sandpile.boxDist_sub_unit 0 i))
  rw [Sandpile.sceneryDeviation, Sandpile.sceneryDeviation, h0, hu, havg]


end Sandpile
