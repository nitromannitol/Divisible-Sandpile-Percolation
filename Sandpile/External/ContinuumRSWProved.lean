import Sandpile.External.ContinuumRSW.FromPlanar
import Sandpile.External.PlanarRSWProved

/-!
# The continuum crossing comparison

The continuum crossing comparison follows from the planar one, which is proved.
-/

/-- The continuum RSW comparison holds. -/
theorem Sandpile.External.continuumRSW_holds : Sandpile.External.ContinuumRSW :=
  Sandpile.External.ContinuumRSW.continuumRSW_of_planarRSW Sandpile.External.planarRSW_holds
