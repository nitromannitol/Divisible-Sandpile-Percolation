/-
Theorem of sandpile.tex giving the optimal-stopping representation of the
odometer, frozen.  `sandpile.tex:857-863` (label `thm:RW`, Theorem 3.2 of the
work cited as `BPSH`):

  "For all $n \geq 0$ and $x\in\Z^d$,
   $u_n(x) = v_n(x) = \mathbf E_x[S_{\tau_n^*}]$,
   where $\tau_n^* \coloneqq \min\{0 \leq k \leq n : v_{n-k}(X_k) = 0\}$."

The paper cites this without proof; it enters through the cited proposition
`Sandpile.External.OptimalStopping`, stated in `Sandpile/External/BPSH.lean`,
and the conclusion below is its instance at a fixed dimension, scenery, time and
site.  All three members of the paper's chain are transcribed: `u_n` is
`Sandpile.odometerOf ζ n`, `v_n` is `Sandpile.stoppingValue ζ n`, and
`E_x[S_{τ_n^*}]` is the integral of `Sandpile.sceneryPartialSum ζ` evaluated at
`Sandpile.optimalStop ζ n` against `Sandpile.walkLaw d x`, where
`Sandpile.optimalStop` is the paper's `τ_n^*` written as an infimum over the
naturals at most `n`.  The dimension carries `1 ≤ d` because at `d = 0` the
averaging operator behind `odometerOf` takes a junk value.

The cited proposition is proved unconditionally in this repository,
`Sandpile.External.optimalStopping` (`Sandpile/External/BPSHProved.lean`), so
it is no longer carried here as an explicit hypothesis.
-/
import Sandpile.External.BPSHProved

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
