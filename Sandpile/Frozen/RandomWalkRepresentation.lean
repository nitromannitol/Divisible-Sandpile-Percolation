import Sandpile.External.BPSHProved

/-!
# The optimal-stopping representation of the odometer

This file proves the frozen statement of `thm:RW` (`sandpile.tex:857-863`, Theorem 3.2 of BPSH):
for every dimension `d ≥ 1`, scenery `ζ`, time `n`, and site `x`, the odometer `u_n(x)`
(`Sandpile.odometerOf ζ n x`) equals the stopping value `v_n(x)` (`Sandpile.stoppingValue ζ n x`),
which in turn equals `E_x[S_{τ_n^*}]`, the expectation under `Sandpile.walkLaw d x` of the
scenery partial sum `Sandpile.sceneryPartialSum ζ` evaluated at the optimal stopping time
`Sandpile.optimalStop ζ n`. The identity is obtained as the instance of the cited proposition
`Sandpile.External.OptimalStopping`, which this repository proves unconditionally as
`Sandpile.External.optimalStopping` rather than carrying as a hypothesis.
-/

open MeasureTheory ProbabilityTheory Filter Topology

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.random_walk_representation
    (d : ℕ) (hd : 1 ≤ d) (ζ : Sandpile.Site d → ℝ) (n : ℕ) (x : Sandpile.Site d) :
    Sandpile.odometerOf ζ n x = Sandpile.stoppingValue ζ n x ∧
      Sandpile.stoppingValue ζ n x =
        ∫ X, Sandpile.sceneryPartialSum ζ (Sandpile.optimalStop ζ n X) X
          ∂(Sandpile.walkLaw d x)
-- FROZEN-STATEMENT-END
:= Sandpile.External.optimalStopping d hd ζ n x
