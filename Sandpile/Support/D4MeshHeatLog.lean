import Sandpile.Support.D4DoubleHeatCentered
import Sandpile.Support.D4MeshDistance
import Sandpile.Support.D4LogKernel
import Sandpile.Support.TightKernel

/-!
# Logarithmic control of the doubled heat kernel on a mesh

After subtracting a spatially constant term, the four-dimensional doubled
heat kernel is bounded by a logarithmic singularity in continuum distance,
uniformly in time and mesh scale.
-/

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

/-- The spatially constant part of the doubled heat kernel at the mesh scale. -/
noncomputable def doubleHeatReference (t : ℕ) (R : ℝ) : ℝ :=
  if 2 ≤ t then 4 / Real.pi ^ 2 * max 0 (Real.log ((t : ℝ) / R ^ 2)) else 0

/-- On bounded sets the centered doubled heat kernel has a uniform logarithmic
continuum singularity, including times zero and one. -/
theorem exists_double_heat_mesh_log_bound (hPaired : External.PairedLocalCLTFour) (L : ℝ) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ t : ℕ, ∀ R : ℝ, 1 ≤ R →
      ∀ u v : Space 4, 0 < ‖u - v‖ → ‖u - v‖ ≤ L →
      |(∑ a ∈ Finset.range t, ∑ b ∈ Finset.range t,
        heatKernel 4 (a + b) (fun i => ⌊R * u i⌋) (fun i => ⌊R * v i⌋)) -
        doubleHeatReference t R| ≤ A + B * logKernel (u - v) := by
  obtain ⟨C, hC, hcent⟩ := exists_double_heat_kernel_four_centered_bound hPaired
  let c : ℝ := 4 / Real.pi ^ 2
  let A : ℝ := max C 1 + c * (Real.log (9 + 2 * L ^ 2) + Real.log 8)
  let B : ℝ := 2 * c
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hlog : 0 ≤ Real.log (9 + 2 * L ^ 2) + Real.log 8 := by
    have h1 : 1 ≤ 9 + 2 * L ^ 2 := by nlinarith [sq_nonneg L]
    exact add_nonneg (Real.log_nonneg h1) (Real.log_nonneg (by norm_num))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨A, B, hA, hB, ?_⟩
  intro t R hR u v huv hL
  let x : Site 4 := fun i => ⌊R * u i⌋
  let y : Site 4 := fun i => ⌊R * v i⌋
  by_cases ht : 2 ≤ t
  · have hbase := hcent t ht R (by linarith : 0 < R) x y
    have hmesh := abs_log_mesh_distance_le R L hR u v huv hL
    have hmul := mul_le_mul_of_nonneg_left hmesh hc
    have hmax : C ≤ max C 1 := le_max_left _ _
    simp only [doubleHeatReference, ite_eq_left ht]
    dsimp only [x, y] at hbase
    dsimp only [A, B, c, logKernel] at *
    nlinarith
  · have ht' : t = 0 ∨ t = 1 := by omega
    have hsmall : |(∑ a ∈ Finset.range t, ∑ b ∈ Finset.range t,
        heatKernel 4 (a + b) x y) - doubleHeatReference t R| ≤ 1 := by
      rcases ht' with rfl | rfl
      · simp [doubleHeatReference]
      · simp only [Finset.range_one, Finset.sum_singleton, add_zero,
          doubleHeatReference, show ¬2 ≤ 1 by omega, ite_false, sub_zero]
        rw [abs_of_nonneg (heatKernel_nonneg 0 x y)]
        exact heatKernel_le_one (by norm_num) 0 x y
    have hk := logKernel_nonneg (u - v)
    have hmax : (1 : ℝ) ≤ max C 1 := le_max_right _ _
    dsimp [A] at hmax ⊢
    exact hsmall.trans (by nlinarith [mul_nonneg hc hlog, mul_nonneg hB hk])

end Sandpile.Support
