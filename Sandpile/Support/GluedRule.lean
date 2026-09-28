import Mathlib
import Sandpile.Walk
import Sandpile.Support.Localization
import Sandpile.Support.EpsilonOptimalRule

/-!
# The glued stopping rule for a localized restart

`gluedRule σ ρ` runs the stopping time `σ`, then continues from the position at time `σ` with
the rule `ρ` attached to that exit position, applied to the path shifted to start there. Since
the choice of `ρ` depends only on the exit point, which two paths agreeing up to that point
share, `isWalkStopping_gluedRule` shows the glued rule is again a stopping rule whenever `σ`
and every rule in the family `ρ` are, bounded by `σ`'s bound plus the localized horizon.
-/

open MeasureTheory
namespace Sandpile

/-- Glue a rule family to a stopping time: run σ, then continue from the
position at time σ with the rule attached to that position. -/
def gluedRule {d : ℕ} (σ : (ℕ → Site d) → ℕ) (ρ : Site d → ((ℕ → Site d) → ℕ))
    (X : ℕ → Site d) : ℕ :=
  σ X + ρ (X (σ X)) (LatticeProb.shiftPath (σ X) X)

/-- The glued rule `gluedRule σ ρ` is again a stopping rule: two paths agreeing up to the
glued time agree on `σ`, on the exit position `X (σ X)`, and hence on the shifted path fed to
`ρ`, so the residual rule and the total time computed from each path coincide. -/
theorem isWalkStopping_gluedRule {d : ℕ} {σ : (ℕ → Site d) → ℕ} (hσ : IsWalkStopping σ)
    {ρ : Site d → ((ℕ → Site d) → ℕ)} (hρ : ∀ y, IsWalkStopping (ρ y)) :
    IsWalkStopping (gluedRule σ ρ) := by
  intro m X Y hXY heq
  -- σ X ≤ m
  have hσX : σ X ≤ m := by
    unfold gluedRule at heq
    omega
  -- σ agrees on the prefix
  have hσeq : σ X = σ Y := (hσ (σ X) X Y (fun j hj => hXY j (le_trans hj hσX)) rfl).symm
  -- the exit positions agree
  have hpos : X (σ X) = Y (σ X) := hXY (σ X) hσX
  -- the shifted paths agree up to m - σ X
  have hshift : ∀ j ≤ m - σ X,
    LatticeProb.shiftPath (σ X) X j = LatticeProb.shiftPath (σ X) Y j := by
    intro j hj
    unfold LatticeProb.shiftPath
    exact hXY (σ X + j) (by omega)
  -- the residual rule agrees
  have hres : ρ (X (σ X)) (LatticeProb.shiftPath (σ X) X) = m - σ X := by
    unfold gluedRule at heq
    omega
  have hres' : ρ (X (σ X)) (LatticeProb.shiftPath (σ X) Y) = m - σ X :=
    hρ (X (σ X)) (m - σ X) (LatticeProb.shiftPath (σ X) X) (LatticeProb.shiftPath (σ X) Y)
      hshift hres
  -- conclude
  unfold gluedRule
  rw [← hσeq, ← hpos, hres']
  omega
