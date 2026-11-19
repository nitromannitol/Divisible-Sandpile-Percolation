import Mathlib

/-!
# Finite truncations of square-summable coefficient families

A square-summable family has a finite restriction whose omitted squared mass is
arbitrarily small. Applied to each row of a triangular array, this yields finite
rows with the same limiting squared mass and the same uniform coefficient bound.
These truncations prepare infinite weighted sums for a finite-row central limit
theorem.
-/

open Filter Topology

namespace Sandpile.Support

/-- A finite restriction captures all but an arbitrarily small part of the
squared mass of a square-summable real family. -/
theorem exists_finset_sq_tail_lt {ι : Type*} (a : ι → ℝ)
    (ha : Summable (fun i => a i ^ 2)) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset ι, (∑' i : (sᶜ : Set ι), a i ^ 2) < ε := by
  classical
  obtain ⟨s, hs⟩ : ∃ s : Finset ι, dist (∑ i ∈ s, a i ^ 2) (∑' i, a i ^ 2) < ε := by
    have hsum := ha.hasSum
    rw [HasSum, Metric.tendsto_nhds] at hsum
    exact (hsum ε hε).exists
  have heq : (∑' i : (sᶜ : Set ι), a i ^ 2) =
      (∑' i, a i ^ 2) - ∑ i ∈ s, a i ^ 2 := by
    linarith [ha.sum_add_tsum_compl (s := s)]
  refine ⟨s, ?_⟩
  rw [heq]
  have := (abs_lt.mp (by simpa only [Real.dist_eq] using hs)).1
  linarith

/-- A family of square-summable rows admits finite restrictions whose squared
masses converge to the same limit whenever the prescribed tail tolerances tend
to zero. -/
theorem exists_finset_rows_sq_tendsto {α ι : Type*} (l : Filter α)
    (a : α → ι → ℝ) (ha : ∀ j, Summable (fun i => a j i ^ 2))
    (ε : α → ℝ) (hε : ∀ j, 0 < ε j) (hεlim : Tendsto ε l (𝓝 0))
    (Q : ℝ) (hQ : Tendsto (fun j => ∑' i, a j i ^ 2) l (𝓝 Q)) :
    ∃ s : α → Finset ι,
      (∀ j, (∑' i : ((s j)ᶜ : Set ι), a j i ^ 2) < ε j) ∧
      Tendsto (fun j => ∑ i ∈ s j, a j i ^ 2) l (𝓝 Q) := by
  classical
  choose s hs using fun j => exists_finset_sq_tail_lt (a j) (ha j) (hε j)
  refine ⟨s, hs, ?_⟩
  have hlower : Tendsto (fun j => (∑' i, a j i ^ 2) - ε j) l (𝓝 Q) := by
    simpa only [sub_zero] using hQ.sub hεlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hQ ?_ ?_
  · exact Filter.Eventually.of_forall fun j => by
      have heq := (ha j).sum_add_tsum_compl (s := s j)
      have htail := hs j
      linarith
  · exact Filter.Eventually.of_forall fun j => by
      have heq := (ha j).sum_add_tsum_compl (s := s j)
      have htail : 0 ≤ ∑' i : ((s j)ᶜ : Set ι), a j i ^ 2 :=
        tsum_nonneg fun i => sq_nonneg _
      linarith

end Sandpile.Support
