/-
The glued stopping rule for the finite-range lower bound of the dimension-four
critical-level percolation argument (`sandpile.tex:3882-3895`): after a
bounded stopping time σ, continue with an ε-optimal localized rule chosen
from the exit point.  The choice of rule depends only on the exit point,
which is determined by the path up to the exit, so the glued rule is again a
stopping rule, bounded by σ's bound plus the localized horizon.
-/
import Mathlib
import Sandpile.Walk
import Sandpile.Support.Localization
import Sandpile.Support.EpsilonOptimalRule

open MeasureTheory
namespace Sandpile

/-- Glue a rule family to a stopping time: run σ, then continue from the
position at time σ with the rule attached to that position. -/
def gluedRule {d : ℕ} (σ : (ℕ → Site d) → ℕ) (ρ : Site d → ((ℕ → Site d) → ℕ)) (X : ℕ → Site d) : ℕ :=
  σ X + ρ (X (σ X)) (LatticeProb.shiftPath (σ X) X)

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
