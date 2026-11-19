import Sandpile.External.Stopping.FiniteIncrementSums

/-!
# Walk convergence at finitely many ordered times

Successive increments telescope to positions relative to the initial time.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace Sandpile.External.Stopping

/-- At finitely many strictly ordered times, the rescaled walk positions
relative to the initial time converge jointly to the Brownian positions. -/
theorem tendstoInDistribution_walk_brownian_finite_ordered_times
    {d m : ℕ} [NeZero d] (R : ℕ → ℝ) (hR : Tendsto R atTop atTop)
    (u : Fin (m + 1) → ℝ≥0) (hu : StrictMono u)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (hB : LatticeProb.IsBrownianSpace d 0 B P) :
    TendstoInDistribution
      (fun n (ξ : ℕ → LatticeProb.Site d) (p : Fin (m + 1) × Fin d) =>
        (R n)⁻¹ * ((∑ k ∈ Finset.range (⌊(u p.1 : ℝ) * (R n) ^ 2⌋₊),
          ((ξ k p.2 : ℤ) : ℝ)) -
          ∑ k ∈ Finset.range (⌊(u 0 : ℝ) * (R n) ^ 2⌋₊),
            ((ξ k p.2 : ℤ) : ℝ)))
      atTop (fun ω (p : Fin (m + 1) × Fin d) => B (u p.1) ω p.2 - B (u 0) ω p.2)
      (fun _ => LatticeProb.incPathLaw d) P := by
  let s : Fin m → ℝ≥0 := fun i => u i.castSucc
  let t : Fin m → ℝ≥0 := fun i => u i.succ
  have hst (i : Fin m) : s i < t i := hu Fin.castSucc_lt_succ
  have hdisj (i j : Fin m) (hij : i ≠ j) : t i ≤ s j ∨ t j ≤ s i := by
    rcases lt_or_gt_of_ne hij with h | h
    · left
      apply hu.monotone
      simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
      exact Nat.succ_le_iff.mpr h
    · right
      apply hu.monotone
      simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
      exact Nat.succ_le_iff.mpr h
  have h := tendstoInDistribution_walk_brownian_cumulative_intervals R hR s t hst hdisj P B hB
  refine h.congr (fun n => Filter.Eventually.of_forall fun ξ => ?_)
    (Filter.Eventually.of_forall fun ω => ?_)
  · funext p
    let f : ℕ → ℝ := fun j => if hj : j < m + 1 then
      (R n)⁻¹ * ∑ k ∈ Finset.range (⌊(u ⟨j, hj⟩ : ℝ) * (R n) ^ 2⌋₊),
        ((ξ k p.2 : ℤ) : ℝ) else 0
    have hterm (i : Fin m) :
        (R n)⁻¹ * ∑ k ∈ Finset.range (⌊(t i : ℝ) * (R n) ^ 2⌋₊ -
          ⌊(s i : ℝ) * (R n) ^ 2⌋₊),
          ((ξ (⌊(s i : ℝ) * (R n) ^ 2⌋₊ + k) p.2 : ℤ) : ℝ) =
        f (i.val + 1) - f i.val := by
      have hfloor : ⌊(s i : ℝ) * (R n) ^ 2⌋₊ ≤ ⌊(t i : ℝ) * (R n) ^ 2⌋₊ := by
        apply Nat.floor_mono
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast (hst i).le) (sq_nonneg _)
      simp only [f, dite_eq_left (by omega : i.val + 1 < m + 1),
        dite_eq_left (by omega : i.val < m + 1)]
      rw [← mul_sub]
      congr 1
      symm
      have heq := Finset.sum_range_add_sub_sum_range
        (fun k => ((ξ k p.2 : ℤ) : ℝ)) (⌊(s i : ℝ) * (R n) ^ 2⌋₊)
        (⌊(t i : ℝ) * (R n) ^ 2⌋₊ - ⌊(s i : ℝ) * (R n) ^ 2⌋₊)
      have hs : (⟨i.val, by omega⟩ : Fin (m + 1)) = i.castSucc := Fin.ext rfl
      have ht : (⟨i.val + 1, by omega⟩ : Fin (m + 1)) = i.succ := Fin.ext rfl
      simpa only [Nat.add_sub_of_le hfloor, s, t, hs, ht] using heq
    simp_rw [hterm]
    rw [sum_fin_initial_differences]
    simp only [f, dite_eq_left p.1.isLt, dite_eq_left (by omega : 0 < m + 1)]
    simp only [Fin.eta, Fin.mk_zero]
    ring
  · funext p
    let f : ℕ → ℝ := fun j => if hj : j < m + 1 then B (u ⟨j, hj⟩) ω p.2 else 0
    have hterm (i : Fin m) : B (t i) ω p.2 - B (s i) ω p.2 =
        f (i.val + 1) - f i.val := by
      have hs : (⟨i.val, by omega⟩ : Fin (m + 1)) = i.castSucc := Fin.ext rfl
      have ht : (⟨i.val + 1, by omega⟩ : Fin (m + 1)) = i.succ := Fin.ext rfl
      simp only [f, dite_eq_left (by omega : i.val + 1 < m + 1),
        dite_eq_left (by omega : i.val < m + 1), s, t, hs, ht]
    simp_rw [hterm, sum_fin_initial_differences]
    simp only [f, dite_eq_left p.1.isLt, dite_eq_left (by omega : 0 < m + 1),
      Fin.eta, Fin.mk_zero]

end Sandpile.External.Stopping
