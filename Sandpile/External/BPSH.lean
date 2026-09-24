/-
External input: the optimal-stopping representation of the divisible sandpile
odometer, Theorem 3.2 of the work cited as `BPSH` in `sandpile.tex`, as the
paper restates it in `thm:RW` (`sandpile.tex:857-863`):

  "For all $n \geq 0$ and $x\in\Z^d$,
   $u_n(x) = v_n(x) = \mathbf E_x[S_{\tau_n^*}]$,
   where $\tau_n^* \coloneqq \min\{0 \leq k \leq n : v_{n-k}(X_k) = 0\}$."

Assumed here.  The paper's `u_n` written in the scenery is
`Sandpile.odometerOf ζ n`, its `v_n` is `Sandpile.stoppingValue ζ n`, its
`S_k` is `Sandpile.sceneryPartialSum ζ k`, and `E_x` is the integral against
`Sandpile.walkLaw d x`.  The scenery `ζ` is an arbitrary real field, which is
the paper's arbitrary initial configuration `σ` through `ζ = (σ - 1)/(2d)`.
The dimension carries `1 ≤ d`, since at `d = 0` the averaging operator behind
`odometerOf` is a junk zero.
-/
import Sandpile.Walk

open MeasureTheory

/-- The optimal stopping time `τ_n^* = min{0 ≤ k ≤ n : v_{n-k}(X_k) = 0}` of
`thm:RW`.  The minimum is over a set of naturals containing `n`, because
`v_0 = 0` for every scenery and site, so this `sInf` is the paper's minimum and
is never the junk value of an empty infimum. -/
noncomputable def Sandpile.optimalStop {d : ℕ} (ζ : Sandpile.Site d → ℝ) (n : ℕ)
    (X : ℕ → Sandpile.Site d) : ℕ :=
  sInf {k : ℕ | k ≤ n ∧ Sandpile.stoppingValue ζ (n - k) (X k) = 0}

-- FROZEN-STATEMENT-BEGIN
/-- Theorem 3.2 of `BPSH`, the optimal-stopping representation `thm:RW`, assumed. -/
def Sandpile.External.OptimalStopping : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (ζ : Sandpile.Site d → ℝ) (n : ℕ) (x : Sandpile.Site d),
    Sandpile.odometerOf ζ n x = Sandpile.stoppingValue ζ n x ∧
      Sandpile.stoppingValue ζ n x =
        ∫ X, Sandpile.sceneryPartialSum ζ (Sandpile.optimalStop ζ n X) X
          ∂(Sandpile.walkLaw d x)
-- FROZEN-STATEMENT-END
