/-
Where a killed walk can be when it stops, and why the cutoff of the proof of
Theorem 1.3(i)(b) costs nothing in the killed problem.

The proof of Theorem 1.3(i)(b) pays two cutoff errors (`sandpile.tex:1908-1922`),
because the reward `-Z_R^{lin}` is not bounded in space and the cited stability
input needs bounded rewards.  In the killed problem of
`rem:dlt4-killed-scaling` those two errors are ZERO: a walk killed on exiting
`Q(⌊Ru⌋,R)` is inside that box at every time strictly before it stops, hence
within one step of it when it stops, so its rescaling never leaves a fixed
neighbourhood of `u`, and a cutoff equal to one there does not change the reward
at any point the killed problem reads.

This module proves the lattice half of that statement: almost every path of the
walk starts where the walk starts and moves by one coordinate step at a time
(`ae_walk_start`, `ae_step_walk`), so the position at a killed stopping time is
within `⌊L⌋+1` of the centre of the box in every coordinate
(`killed_position_box`), and its rescaling is within `√d(⌊L⌋+1)/R` of the
rescaled centre (`norm_scaledSite_sub_le`).
-/
import Sandpile.Support.KillRep
import Sandpile.Support.ContLcltPoint
import Sandpile.Frozen.MeanLocalization

open MeasureTheory
open scoped NNReal

namespace Sandpile

variable {d : ℕ}

/-- Almost every path of the walk starts where the walk starts. -/
theorem ae_walk_start (x : Site d) : ∀ᵐ X ∂(walkLaw d x), X 0 = x := by
  have hmeas : MeasurableSet {X : ℕ → Site d | X 0 = x} := by
    have hrw : {X : ℕ → Site d | X 0 = x} = (fun X : ℕ → Site d => X 0) ⁻¹' {x} := rfl
    rw [hrw]
    exact (measurable_pi_apply 0) (Set.to_countable _).measurableSet
  rw [walkLaw, ae_map_iff (measurable_walkPath x).aemeasurable hmeas]
  exact Filter.Eventually.of_forall fun ξ => walkPath_zero x ξ

/-- Almost every path of the walk moves by one coordinate step at a time. -/
theorem ae_step_walk (hd : 1 ≤ d) (x : Site d) :
    ∀ᵐ X ∂(walkLaw d x), ∀ (n : ℕ) (i : Fin d), ((X (n + 1)) i - (X n) i).natAbs ≤ 1 := by
  have hmeas : MeasurableSet
      {X : ℕ → Site d | ∀ (n : ℕ) (i : Fin d), ((X (n + 1)) i - (X n) i).natAbs ≤ 1} := by
    have hrw : {X : ℕ → Site d | ∀ (n : ℕ) (i : Fin d), ((X (n + 1)) i - (X n) i).natAbs ≤ 1}
        = ⋂ n : ℕ, (fun X : ℕ → Site d => (X n, X (n + 1))) ⁻¹'
            {p : Site d × Site d | ∀ i, ((p.2) i - (p.1) i).natAbs ≤ 1} := by
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    rw [hrw]
    refine MeasurableSet.iInter fun n => ?_
    exact ((measurable_pi_apply n).prodMk (measurable_pi_apply (n + 1)))
      (Set.to_countable _).measurableSet
  rw [walkLaw, ae_map_iff (measurable_walkPath x).aemeasurable hmeas]
  filter_upwards [ae_mem_stepSet hd] with ξ hξ n i
  have hstep : walkPath x ξ (n + 1) = walkPath x ξ n + ξ n := by
    unfold walkPath
    rw [Finset.sum_range_succ, ← add_assoc]
  rw [hstep]
  obtain ⟨j, hj | hj⟩ := hξ n
  · have : (walkPath x ξ n + ξ n) i - walkPath x ξ n i = (unit j : Site d) i := by
      rw [hj]; simp
    rw [this]
    exact natAbs_unit_le j i
  · have : (walkPath x ξ n + ξ n) i - walkPath x ξ n i = -((unit j : Site d) i) := by
      rw [hj]; simp
    rw [this, Int.natAbs_neg]
    exact natAbs_unit_le j i

/-- **A killed walk is within one step of its box when it stops.**  The killing condition
places the path in `Q(x₀,L)` at every time strictly before the stopping time, and one step
moves each coordinate by at most one. -/
theorem killed_position_box {x₀ : Site d} {L : ℝ} (hL : 0 ≤ ⌊L⌋) {X : ℕ → Site d}
    (h0 : X 0 = x₀) (hstep : ∀ (n : ℕ) (i : Fin d), ((X (n + 1)) i - (X n) i).natAbs ≤ 1)
    (k : ℕ) (hk : ∀ j < k, X j ∈ supBox x₀ L) (i : Fin d) :
    |X k i - x₀ i| ≤ ⌊L⌋ + 1 := by
  cases k with
  | zero =>
      rw [h0]
      simp only [sub_self, abs_zero]
      omega
  | succ m =>
      have hm : X m ∈ supBox x₀ L := hk m (by omega)
      have h1 : |X m i - x₀ i| ≤ ⌊L⌋ := hm i
      rw [abs_le] at h1
      have h2 := hstep m i
      rw [abs_le]
      omega

/-- A vector of `ℝ^d` whose coordinates are at most `c` in absolute value has norm at most
`√d · c`. -/
theorem Continuum.norm_le_of_coord_le {v : Sandpile.Continuum.Space d} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i, |v i| ≤ c) : ‖v‖ ≤ Real.sqrt d * c := by
  rw [EuclideanSpace.norm_eq]
  have hsum : ∑ i : Fin d, ‖v i‖ ^ 2 ≤ (d : ℝ) * c ^ 2 := by
    calc ∑ i : Fin d, ‖v i‖ ^ 2 ≤ ∑ _i : Fin d, c ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [Real.norm_eq_abs, sq_abs]
          have hi := h i
          rw [abs_le] at hi
          exact sq_le_sq' (by linarith) (by linarith)
      _ = (d : ℝ) * c ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc Real.sqrt (∑ i : Fin d, ‖v i‖ ^ 2) ≤ Real.sqrt ((d : ℝ) * c ^ 2) :=
        Real.sqrt_le_sqrt hsum
    _ = Real.sqrt d * c := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hc]

/-- The rescalings of two sites whose coordinates differ by at most `m` are within
`√d · m / R`. -/
theorem norm_scaledSite_sub_le {R : ℝ} (hR : 0 < R) (y x₀ : Site d) {m : ℝ} (hm : 0 ≤ m)
    (h : ∀ i, |((y i : ℤ) : ℝ) - ((x₀ i : ℤ) : ℝ)| ≤ m) :
    ‖Sandpile.External.Lclt.scaledSite R y - Sandpile.External.Lclt.scaledSite R x₀‖
      ≤ Real.sqrt d * m / R := by
  have hc : ∀ i : Fin d, |(Sandpile.External.Lclt.scaledSite R y
      - Sandpile.External.Lclt.scaledSite R x₀) i| ≤ m / R := by
    intro i
    have hval : (Sandpile.External.Lclt.scaledSite R y
        - Sandpile.External.Lclt.scaledSite R x₀) i
        = (((y i : ℤ) : ℝ) - ((x₀ i : ℤ) : ℝ)) / R := by
      show ((y i : ℤ) : ℝ) / R - ((x₀ i : ℤ) : ℝ) / R = _
      ring
    rw [hval, abs_div, abs_of_pos hR]
    exact div_le_div_of_nonneg_right (h i) hR.le
  have := Continuum.norm_le_of_coord_le (v := Sandpile.External.Lclt.scaledSite R y
      - Sandpile.External.Lclt.scaledSite R x₀) (by positivity) hc
  calc ‖Sandpile.External.Lclt.scaledSite R y - Sandpile.External.Lclt.scaledSite R x₀‖
      ≤ Real.sqrt d * (m / R) := this
    _ = Real.sqrt d * m / R := by ring

end Sandpile
