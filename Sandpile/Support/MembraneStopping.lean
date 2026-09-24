/-
The membrane field is a competitor in the optimal-stopping problem.

Stopping the walk at a deterministic time `n` collects exactly the membrane
field `V_n`, so `V_n(x) ≤ u_t(x)` whenever `n ≤ t`.  This is the "deterministic
stopping" step of the proof of `thm:critical-toppling`, which tests the odometer
against the membrane field at a geometric sequence of times.
-/
import Sandpile.Support.Localization

open MeasureTheory

namespace Sandpile

variable {d : ℕ}

/-- A deterministic time is a stopping time of the walk. -/
theorem isWalkStopping_const (n : ℕ) : IsWalkStopping (fun _ : ℕ → Site d => n) := by
  intro k X Y _ h
  exact h

/-- The scenery collected up to a deterministic time integrates to the membrane
field: `E_x ∑_{k<n} ζ(X_k) = V_n(x)`. -/
theorem integral_sceneryPartialSum_eq_membrane (hd : 1 ≤ d) (x : Site d)
    (ζ : Site d → ℝ) (n : ℕ) :
    ∫ X, sceneryPartialSum ζ n X ∂(walkLaw d x) = membrane ζ n x := by
  have h := Sandpile.integral_neg_stoppedMembrane hd x ζ n (isWalkStopping_const n) (fun _ => le_refl n)
  simp only [Nat.sub_self, membrane_zero, neg_zero, integral_zero] at h
  linarith

/-- **The membrane field is below the odometer**: for `n ≤ t`,
`V_n(x) ≤ u_t(x)`. -/
theorem membrane_le_odometerOf (hd : 1 ≤ d) (ζ : Site d → ℝ) {n t : ℕ} (h : n ≤ t)
    (x : Site d) :
    membrane ζ n x ≤ odometerOf ζ t x := by
  have h1 := integral_stoppedScenery_le_odometer External.optimalStopping hd ζ t x
    (ρ := fun _ : ℕ → Site d => n) (isWalkStopping_const n) (fun _ => h)
  rwa [integral_sceneryPartialSum_eq_membrane hd x ζ n] at h1

end Sandpile
