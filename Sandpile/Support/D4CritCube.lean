/-
Identifications among the boxes of the dimension-four percolation argument and
the translation covariance of the walk, the ingredients Step 1 of
`thm:d4-critical-level-percolation` (`sandpile.tex:4001-4026`) needs to read the
exit average of `lem:d4-exit-average-concentration` against the localized mean
of `cor:mean-localization`.
-/
import Sandpile.Frozen.D4ExitAverageConcentration
import Sandpile.Frozen.MeanLocalization
import Sandpile.Frozen.D4FiniteRangeLowerBound
import Sandpile.Support.BallCrossingDefinitions
import Sandpile.Support.Localization

namespace Sandpile

/-- The real-radius sup box and the floor-radius sup box are the same set. -/
theorem eaCube_eq_supBox (x : Site 4) (L : ℝ) : eaCube x L = supBox x L := by
  ext y
  simp only [Sandpile.eaCube, Sandpile.supBox, Set.mem_setOf_eq]
  constructor
  · intro h i
    have hi := h i
    rw [Int.le_floor]
    rw [Int.cast_abs, Int.cast_sub]
    exact hi
  · intro h i
    have hi := h i
    rw [Int.le_floor] at hi
    rw [Int.cast_abs, Int.cast_sub] at hi
    exact hi

theorem eaCube_eq_ballCube (x : Site 4) (L : ℝ) : eaCube x L = ballCube x L := rfl

theorem eaCube_eq_frCube (x : Site 4) (L : ℝ) : eaCube x L = frCube x L := rfl

/-- Translating the path translates the exit set. -/
theorem exitTime_translate {d : ℕ} (D : Set (Site d)) (x : Site d) (X : ℕ → Site d) :
    exitTime {y : Site d | x + y ∈ D} X = exitTime D (fun k => x + X k) := rfl

/-- The walk is outside `D` at the stopped time exactly when it has left `D`
by time `N`. -/
theorem notMem_stopBeforeExit_iff {d : ℕ} (D : Set (Site d)) (N : ℕ) (X : ℕ → Site d) :
    X (stopBeforeExit D N (fun _ => N) X) ∉ D ↔ exitNat D N X ≤ N := by
  constructor
  · intro h
    by_contra hc
    have hmin : stopBeforeExit D N (fun _ => N) X = N := min_eq_left (le_of_not_ge hc)
    rw [hmin] at h
    exact h (mem_of_lt_exitNat (by omega) le_rfl)
  · intro h
    have hmin : stopBeforeExit D N (fun _ => N) X = exitNat D N X := min_eq_right h
    rw [hmin]
    exact notMem_exitNat h

end Sandpile
