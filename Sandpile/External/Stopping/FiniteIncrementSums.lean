import Sandpile.External.Stopping.WalkCumulativeIntervals

/-!
# Finite sums of successive increments

A cumulative sum over the first terms of a finite family of successive
increments telescopes to the difference of its endpoints.
-/

namespace Sandpile.External.Stopping

/-- The sum of successive differences before an index equals the difference
between the indexed term and the initial term. -/
theorem sum_fin_initial_differences {m : ℕ} (f : ℕ → ℝ) (i : Fin (m + 1)) :
    (∑ j : Fin m, if j.val < i.val then f (j.val + 1) - f j.val else 0) =
      f i.val - f 0 := by
  let g : ℕ → ℝ := fun j => if j < i.val then f (j + 1) - f j else 0
  have hi : i.val ≤ m := by omega
  calc
    _ = ∑ j ∈ Finset.range m, g j := by
      exact Fin.sum_univ_eq_sum_range g m
    _ = ∑ j ∈ Finset.range i.val, g j := by
      symm
      apply Finset.sum_subset (Finset.range_mono hi)
      intro j hj hj'
      have hjn : ¬ j < i.val := by simpa only [Finset.mem_range] using hj'
      simp [g, hjn]
    _ = ∑ j ∈ Finset.range i.val, (f (j + 1) - f j) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [g, Finset.mem_range.mp hj]
    _ = f i.val - f 0 := Finset.sum_range_sub f i.val

end Sandpile.External.Stopping
