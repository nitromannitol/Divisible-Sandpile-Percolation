import Sandpile.External.Stopping.FiniteIncrementSums

/-!
# Walk convergence at ordered times

Successive increments telescope to positions relative to the initial time.
Together with convergence of the increments, this gives finite-dimensional
convergence at any strictly increasing sequence of times.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace Sandpile.External.Stopping

/-- At strictly ordered times, the rescaled walk positions relative to the
initial time converge jointly to the corresponding Brownian positions. -/
theorem tendstoInDistribution_walk_brownian_ordered_times
    {d m : ℕ} [NeZero d] (R : ℕ → ℝ) (hR : Tendsto R atTop atTop)
    (u : ℕ → ℝ≥0) (hu : StrictMono u)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (hB : LatticeProb.IsBrownianSpace d 0 B P) :
    TendstoInDistribution
      (fun n (ξ : ℕ → LatticeProb.Site d) (p : Fin (m + 1) × Fin d) =>
        (R n)⁻¹ * ((∑ k ∈ Finset.range (⌊(u p.1.val : ℝ) * (R n) ^ 2⌋₊),
          ((ξ k p.2 : ℤ) : ℝ)) -
          ∑ k ∈ Finset.range (⌊(u 0 : ℝ) * (R n) ^ 2⌋₊),
            ((ξ k p.2 : ℤ) : ℝ)))
      atTop (fun ω (p : Fin (m + 1) × Fin d) => B (u p.1.val) ω p.2 - B (u 0) ω p.2)
      (fun _ => LatticeProb.incPathLaw d) P := by
  let s : Fin m → ℝ≥0 := fun i => u i.val
  let t : Fin m → ℝ≥0 := fun i => u (i.val + 1)
  have hst (i : Fin m) : s i < t i := hu (Nat.lt_succ_self _)
  have hdisj (i j : Fin m) (hij : i ≠ j) : t i ≤ s j ∨ t j ≤ s i := by
    rcases lt_or_gt_of_ne hij with h | h
    · left
      exact hu.monotone (by simpa only [Fin.lt_def] using Nat.succ_le_iff.mpr h)
    · right
      exact hu.monotone (by simpa only [Fin.lt_def] using Nat.succ_le_iff.mpr h)
  have h := tendstoInDistribution_walk_brownian_cumulative_intervals R hR s t hst hdisj P B hB
  refine h.congr (fun n => Filter.Eventually.of_forall fun ξ => ?_)
    (Filter.Eventually.of_forall fun ω => ?_)
  · funext p
    let f : ℕ → ℝ := fun j => (R n)⁻¹ * ∑ k ∈ Finset.range (⌊(u j : ℝ) * (R n) ^ 2⌋₊),
      ((ξ k p.2 : ℤ) : ℝ)
    have hterm (i : Fin m) :
        (R n)⁻¹ * ∑ k ∈ Finset.range (⌊(t i : ℝ) * (R n) ^ 2⌋₊ -
          ⌊(s i : ℝ) * (R n) ^ 2⌋₊),
          ((ξ (⌊(s i : ℝ) * (R n) ^ 2⌋₊ + k) p.2 : ℤ) : ℝ) =
        f (i.val + 1) - f i.val := by
      have hfloor : ⌊(s i : ℝ) * (R n) ^ 2⌋₊ ≤ ⌊(t i : ℝ) * (R n) ^ 2⌋₊ := by
        apply Nat.floor_mono
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast (hst i).le) (sq_nonneg _)
      dsimp only [f]
      rw [← mul_sub]
      congr 1
      symm
      have heq := Finset.sum_range_add_sub_sum_range
        (fun k => ((ξ k p.2 : ℤ) : ℝ)) (⌊(s i : ℝ) * (R n) ^ 2⌋₊)
        (⌊(t i : ℝ) * (R n) ^ 2⌋₊ - ⌊(s i : ℝ) * (R n) ^ 2⌋₊)
      simpa only [Nat.add_sub_of_le hfloor, s, t] using heq
    simp_rw [hterm]
    rw [sum_fin_initial_differences]
    dsimp only [f]
    ring
  · funext p
    exact sum_fin_initial_differences (fun j => B (u j) ω p.2) p.1

end Sandpile.External.Stopping
