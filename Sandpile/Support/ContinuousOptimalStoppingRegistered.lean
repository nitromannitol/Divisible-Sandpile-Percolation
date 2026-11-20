import Sandpile.Support.ContinuumOptimalStoppingProved

/-!
# Continuous Brownian optimal stopping

The finite-horizon optimal-stopping theorem holds for Brownian paths that
are continuous everywhere and have strongly measurable time slices.
-/

/-- First contact attains the Brownian stopping value and is minimal among
optimal stopping times for continuous paths with measurable time slices. -/
-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.External.continuousOptimalStopping_holds
    {Ω : Type*} [MeasurableSpace Ω] :
    Sandpile.External.ContinuumOptimalStoppingOfContinuous Ω
-- FROZEN-STATEMENT-END
:= Sandpile.External.continuumOptimalStoppingOfContinuous_holds
