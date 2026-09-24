/-
Localization lemma of sandpile.tex, frozen.  `sandpile.tex:1612-1617`
(label `lem:localization-killing`):

  "For every $D\subseteq\Z^d$, every $x\in D$, and every $t\geq0$,
   \[
     0\leq u_t(x)-u_t^D(x)
     \leq\mathbf E_x\bigl[\mathbf 1_{\{\tau_D\leq t\}} u_t(X_{\tau_D})\bigr]\, .
   \]"

Modelling.  `u_t` is `Sandpile.odometerOf ζ t` and `u_t^D` is
`Sandpile.localizedOdometer D ζ t`, both driven by a deterministic scenery `ζ`;
the lemma is a pathwise statement about a fixed scenery, so no law appears.
The right-hand side is an integral against `Sandpile.walkLaw d x`, the law of
simple random walk started at `x` on path space `ℕ → Site d`.

`Sandpile.exitTime D X` has type `ℕ∞`, so the event `\{\tau_D\leq t\}` is
`{X | exitTime D X ≤ (t : ℕ∞)}` and the walk is evaluated at
`(exitTime D X).toNat`.  On the complement of that event the exit time may be
`⊤`, where `toNat` takes the junk value `0`; the integrand is written with
`Set.indicator` of the event, so the junk value is multiplied by zero and never
read.  On the event itself the exit time is a genuine natural number and
`toNat` inverts the coercion.

The dimension hypothesis `1 ≤ d` is the paper's standing assumption: at `d = 0`
the step law of the walk degenerates and both sides take junk values.

The paper's proof writes the odometer as the value of the stopping problem, which
is the optimal-stopping representation, a cited result rather than a theorem of
the paper; it therefore enters as the explicit hypothesis `hOS`, as it does in
`thm:RW` and in `lem:difference-representation`.
-/
import Sandpile.Walk
import Sandpile.External.BPSH
import Sandpile.Support.Localization

open MeasureTheory ProbabilityTheory Filter Topology

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.localization_killing
    (hOS : Sandpile.External.OptimalStopping)
    (d : ℕ) (hd : 1 ≤ d) (ζ : Sandpile.Site d → ℝ) (D : Set (Sandpile.Site d))
    (x : Sandpile.Site d) (hx : x ∈ D) (t : ℕ) :
    0 ≤ Sandpile.odometerOf ζ t x - Sandpile.localizedOdometer D ζ t x ∧
      Sandpile.odometerOf ζ t x - Sandpile.localizedOdometer D ζ t x ≤
        ∫ X, Set.indicator {X : ℕ → Sandpile.Site d | Sandpile.exitTime D X ≤ (t : ℕ∞)}
            (fun X => Sandpile.odometerOf ζ t (X (Sandpile.exitTime D X).toNat)) X
          ∂(Sandpile.walkLaw d x)
-- FROZEN-STATEMENT-END
:= by
  refine ⟨sub_nonneg.mpr (Sandpile.localizedOdometer_le hOS hd D ζ t x hx), ?_⟩
  have hEq : (∫ X, Set.indicator
        {X : ℕ → Sandpile.Site d | Sandpile.exitTime D X ≤ (t : ℕ∞)}
        (fun X => Sandpile.odometerOf ζ t (X (Sandpile.exitTime D X).toNat)) X
        ∂(Sandpile.walkLaw d x))
      = ∫ X, Sandpile.exitReward D ζ t X ∂(Sandpile.walkLaw d x) := rfl
  rw [hEq]
  exact Sandpile.odometerOf_sub_localizedOdometer_le hOS hd D ζ t x hx
