import Sandpile.External.Stopping.CubeStabilityFromCompleted
import Sandpile.External.Stopping.CubeValueRawClock

/-!
# Cube-killed stopping stability

The stability of cube-killed optimal-stopping values follows from the uniform
lower and upper bounds for diffusively rescaled killed lattice walks.  The upper
bound compares the lattice values with the cube-killed Brownian value over
stopping times whose stopping events are measurable up to null sets, through
joint path-clock weak limits and causal randomized stops (Coquet and Toldo,
Theorem 3 and Corollary 4).  That value equals the raw cube-killed Brownian value
because the truncated cube exit agrees almost surely with a stopping time of the
raw natural filtration.
-/

namespace Sandpile.External

/-- The cube-killed stopping stability input holds for Brownian motion in every
positive dimension. -/
theorem cubeStoppingStability_holds : CubeStoppingStability := by
  apply cubeStoppingStability_of_completed_value_eq
  intro d _ Ω _ P _ x B hB T G hGc M hG
  exact Stopping.sSup_aeCubeClockPayoffs_eq_brownianDiscountCube_of_isBrownian
    P x B hB T G hGc M hG

end Sandpile.External
