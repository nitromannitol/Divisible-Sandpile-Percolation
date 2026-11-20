import Sandpile.External.Stopping.KilledStepCompletion

/-!
# Truncated finite exit indices

A lattice exit stopped at a deterministic horizon is the minimum of that
horizon and the finite exit index.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- A truncated lattice exit is the minimum of the horizon and the exit index
when the exit time is finite. -/
theorem stopBeforeExit_const_eq_min_exitTime_toNat {d : ℕ}
    (D : Set (Site d)) (N : ℕ) (X : ℕ → Site d)
    (hfin : Sandpile.exitTime D X ≠ ⊤) :
    stopBeforeExit D N (fun _ => N) X = min N (Sandpile.exitTime D X).toNat := by
  by_cases h : exitNat D N X ≤ N
  · have he := exitTime_eq_exitNat h
    rw [he, ENat.toNat_natCast]
    rfl
  · have he : (N : ℕ∞) ≤ Sandpile.exitTime D X := by
      apply le_of_not_ge
      intro he
      exact h (exitTime_le_iff.mp he)
    have hn : N ≤ (Sandpile.exitTime D X).toNat := by
      simpa only [ENat.toNat_natCast] using ENat.toNat_le_toNat he hfin
    change min N (exitNat D N X) = min N (Sandpile.exitTime D X).toNat
    rw [min_eq_left (le_of_not_ge h), min_eq_left hn]

end Sandpile.External.Stopping
