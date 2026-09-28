import Sandpile.Walk
import Sandpile.External.BPSHProved
import Sandpile.Support.Localization

/-!
# The localization-killing lemma, frozen

Localization lemma of `sandpile.tex`, frozen (`sandpile.tex:1612-1617`, label
`lem:localization-killing`): for a deterministic scenery `ζ`, every `D ⊆ ℤ^d`, `x ∈ D`, and
`t ≥ 0`, the deficit `u_t(x) - u_t^D(x)` between the full and the `D`-localized odometer is
nonnegative and bounded above by the expected reward `E_x[1_{τ_D ≤ t} u_t(X_{τ_D})]`, an integral
against the simple random walk law `Sandpile.walkLaw d x` on path space. Since
`Sandpile.exitTime D X` has type `ℕ∞`, the event `{τ_D ≤ t}` is written with `Set.indicator` so
that the junk value `(⊤).toNat = 0` on its complement is multiplied by zero and never read. The
paper's proof invokes the optimal-stopping representation of the odometer as a cited result, now
proved unconditionally as `Sandpile.External.optimalStopping`, so it is no longer carried here as
an explicit hypothesis.
-/

open MeasureTheory ProbabilityTheory Filter Topology

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.localization_killing
    (d : ℕ) (hd : 1 ≤ d) (ζ : Sandpile.Site d → ℝ) (D : Set (Sandpile.Site d))
    (x : Sandpile.Site d) (hx : x ∈ D) (t : ℕ) :
    0 ≤ Sandpile.odometerOf ζ t x - Sandpile.localizedOdometer D ζ t x ∧
      Sandpile.odometerOf ζ t x - Sandpile.localizedOdometer D ζ t x ≤
        ∫ X, Set.indicator {X : ℕ → Sandpile.Site d | Sandpile.exitTime D X ≤ (t : ℕ∞)}
            (fun X => Sandpile.odometerOf ζ t (X (Sandpile.exitTime D X).toNat)) X
          ∂(Sandpile.walkLaw d x)
-- FROZEN-STATEMENT-END
:= by
  refine ⟨sub_nonneg.mpr
    (Sandpile.localizedOdometer_le Sandpile.External.optimalStopping hd D ζ t x hx), ?_⟩
  have hEq : (∫ X, Set.indicator
        {X : ℕ → Sandpile.Site d | Sandpile.exitTime D X ≤ (t : ℕ∞)}
        (fun X => Sandpile.odometerOf ζ t (X (Sandpile.exitTime D X).toNat)) X
        ∂(Sandpile.walkLaw d x))
      = ∫ X, Sandpile.exitReward D ζ t X ∂(Sandpile.walkLaw d x) := rfl
  rw [hEq]
  exact Sandpile.odometerOf_sub_localizedOdometer_le
    Sandpile.External.optimalStopping hd D ζ t x hx
