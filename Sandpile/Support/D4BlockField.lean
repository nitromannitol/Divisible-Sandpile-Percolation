/-
The block field of the dimension-four critical-level percolation argument
(`sandpile.tex:3860-3880`): the finite-time killed Green field
`𝓑_{r,N}(z) = ∑_u g_N^{Q(0,r)}(0,u) ζ(z+u)` and the localized exit term
`Y_r(z)`, together with the finite-range lower bound
`lem:d4-finite-range-lower-bound`:
`𝓑_{r,A r²}(z) + Y_r(z) ≤ u_{(A+1) r²}(z)`.
-/
import Mathlib
import Sandpile.Support.Killed
import Sandpile.Support.KilledWalk
import Sandpile.Support.Localization
import Sandpile.Support.ExitTail
import Sandpile.Support.BallCrossingDefinitions

open MeasureTheory
noncomputable section
namespace Sandpile

/-- The finite-time killed Green field
`𝓑_{r,N}(z) = ∑_u g_N^{Q(0,r)}(0,u) ζ(z+u)` of `sandpile.tex:3858`. -/
def ballGreenFieldTime (r N : ℕ) (ζ : Site 4 → ℝ) (z : Site 4) : ℝ :=
  killedGreenPair (ballCube 0 (r : ℝ)) N ζ z

/-- The paper's shape of the finite-time ball Green field: the kernel killed
on the ball cube, paired with the shifted scenery (`sandpile.tex:3858`). -/
theorem ballGreenFieldTime_eq_tsum (r N : ℕ) (ζ : Site 4 → ℝ) (z : Site 4) :
    ballGreenFieldTime r N ζ z
      = ∑' u : Site 4,
          killedGreenTime {w : Site 4 | w + z ∈ ballCube 0 (r : ℝ)} N 0 u * ζ (z + u) := by
  rw [ballGreenFieldTime]
  exact (tsum_killedGreenTime_shift (ballCube 0 (r : ℝ)) N z ζ).symm

/-- The exit time of the walk started at `z` from the ball cube
`Q(z,r)`, in the shifted coordinates of `futureHeight`. -/
def cubeExitTime (r : ℕ) (z : Site 4) (X : ℕ → Site 4) : ℕ∞ :=
  exitTime (ballCube 0 (r : ℝ)) (fun j => z + X j)

/-- The localized exit term
`Y_r(z) = E_z[1_{τ_{Q(z,r)} ≤ A r²} · u^{Q(X_τ, A_loc r)}_{r²}(X_τ) | ζ]`
of `sandpile.tex:3865`.  The walk law is independent of the scenery, so the
conditional expectation is the plain integral over path space; the walk
started at `z` is the walk started at `0` translated by `z`. -/
def futureHeight (r A A_loc : ℕ) (ζ : Site 4 → ℝ) (z : Site 4) : ℝ :=
  ∫ X : ℕ → Site 4, Set.indicator
      {X : ℕ → Site 4 | cubeExitTime r z X ≤ ((A * r ^ 2 : ℕ) : ℕ∞)}
      (fun X => localizedOdometer (ballCube 0 ((A_loc * r : ℕ) : ℝ)) ζ (r ^ 2)
        (z + X ((cubeExitTime r z X).toNat))) X
    ∂(walkLaw 4 0)

end Sandpile