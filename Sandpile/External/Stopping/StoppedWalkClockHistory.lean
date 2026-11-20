import Sandpile.External.Stopping.WalkStoppingFiltration

/-!
# History of a truncated discrete stopping time

A stopping rule truncated at a fixed lattice time is determined by the walk
history through that time. This expresses the past-clock information needed
for independence from later increments.
-/

namespace Sandpile.External.Stopping

/-- A discrete stopping rule truncated at `k` depends only on the path
through `k`. -/
theorem IsWalkStopping.min_eq_of_history {d : ℕ} {τ : (ℕ → Site d) → ℕ}
    (hτ : IsWalkStopping τ) (X Y : ℕ → Site d) (k : ℕ)
    (hXY : ∀ j ≤ k, X j = Y j) : min (τ X) k = min (τ Y) k := by
  by_cases hx : τ X ≤ k
  · have h := IsWalkStopping.eq_of_history_le hτ X Y k hXY hx
    rw [h]
  · by_cases hy : τ Y ≤ k
    · have h := IsWalkStopping.eq_of_history_le hτ Y X k (fun j hj => (hXY j hj).symm) hy
      rw [h] at hx
      exact (hx hy).elim
    · rw [min_eq_right (le_of_not_ge hx), min_eq_right (le_of_not_ge hy)]

end Sandpile.External.Stopping
