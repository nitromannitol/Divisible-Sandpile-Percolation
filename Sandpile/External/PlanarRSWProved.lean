import Sandpile.External.RSW.PlanarRSWAdjacentReduction
import Sandpile.External.RSW.AdjacentSixEventProved

/-!
# Planar RSW for positively associated site percolation

The planar comparison follows from the adjacent-scale quasi-crossing
construction and the bridge induction.
-/

/-- The universal planar RSW comparison holds. -/
theorem Sandpile.External.planarRSW_holds : Sandpile.External.PlanarRSW :=
  Sandpile.External.RSW.planarRSW_of_six_event
    Sandpile.External.RSW.kstAdjacentSixEvent_subset_quasi
