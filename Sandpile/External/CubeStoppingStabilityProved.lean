import Sandpile.External.Stopping.CubeStabilityFromCompleted
import Sandpile.External.Stopping.CubeValueRawClock

/-!
# Cube-killed stopping stability, proved

This module discharges the external input `Sandpile.External.CubeStoppingStability`, the
stability of cube-killed optimal-stopping values (Coquet and Toldo, Theorem 3 and Corollary 4),
instead of assuming it.

The lower bound, Brownian value at most lattice value plus `ε`, comes from coupling the
diffusively rescaled walk with the Brownian motion and transferring finite Brownian stopping
rules, clipped at the converging exit clocks, to the walk.  The upper bound compares the lattice
values with the cube-killed Brownian value over stopping times whose stopping events are
measurable up to null sets, through joint path-clock weak limits and causal randomized stops, as
in Coquet and Toldo, Section 2.3.1.  That value equals the raw cube-killed Brownian value of the
statement because the open-cube exit truncated at the horizon agrees almost surely with a
stopping time of the raw natural filtration
(`Sandpile.External.Stopping.isBrownianStopping_rawExitClock`).

The `Prop` and its name are left untouched, so no frozen statement changes.
-/

-- FROZEN-STATEMENT-BEGIN
/-- The stability of cube-killed optimal-stopping values, proved rather than assumed. -/
theorem Sandpile.External.cubeStoppingStability_holds : Sandpile.External.CubeStoppingStability
-- FROZEN-STATEMENT-END
:= by
  apply Sandpile.External.cubeStoppingStability_of_completed_value_eq
  intro d _ Ω _ P _ x B hB T G hGc M hG
  exact Sandpile.External.Stopping.sSup_aeCubeClockPayoffs_eq_brownianDiscountCube_of_isBrownian
    P x B hB T G hGc M hG
