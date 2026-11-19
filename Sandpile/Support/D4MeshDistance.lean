import Sandpile.Support.D4LogRatio
import Sandpile.Support.ContMeshPoint

/-!
# Distance comparison for the four-dimensional lattice mesh

The squared lattice displacement, with one added, is comparable to the
squared continuum displacement at the mesh scale.
-/

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

/-- The difference of two floor errors has absolute value at most one. -/
theorem abs_sub_floor_sub_le_one (x y : ℝ) :
    |(x - y) - ((⌊x⌋ : ℝ) - (⌊y⌋ : ℝ))| ≤ 1 := by
  have hx := Int.floor_le x
  have hx' := Int.lt_floor_add_one x
  have hy := Int.floor_le y
  have hy' := Int.lt_floor_add_one y
  rw [abs_le]
  constructor <;> linarith

/-- The mesh squared distance controls the continuum squared distance and is
itself controlled by it, uniformly at scales at least one. -/
theorem mesh_distance_sq_bounds (R : ℝ) (hR : 1 ≤ R) (u v : Space 4) :
    let q : ℝ := ∑ i : Fin 4,
      (((⌊R * u i⌋ - ⌊R * v i⌋ : ℤ) : ℝ) ^ 2)
    ‖u - v‖ ^ 2 / 8 ≤ (1 + q) / R ^ 2 ∧
      (1 + q) / R ^ 2 ≤ 9 + 2 * ‖u - v‖ ^ 2 := by
  dsimp only
  let q : ℝ := ∑ i : Fin 4,
      (((⌊R * u i⌋ - ⌊R * v i⌋ : ℤ) : ℝ) ^ 2)
  let p : ℝ := ∑ i : Fin 4, (R * (u i - v i)) ^ 2
  have hpq : p ≤ 2 * q + 8 := by
    have hh : p ≤ ∑ i : Fin 4,
        (2 * (((⌊R * u i⌋ - ⌊R * v i⌋ : ℤ) : ℝ) ^ 2) + 2) := by
      apply Finset.sum_le_sum
      intro i _
      have h := abs_sub_floor_sub_le_one (R * u i) (R * v i)
      have hh' := (abs_le.mp h)
      push_cast at hh' ⊢
      nlinarith [sq_nonneg (R * (u i - v i) - 2 *
        ((⌊R * u i⌋ : ℝ) - (⌊R * v i⌋ : ℝ)))]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] at hh
    norm_num at hh
    simpa only [q, Int.cast_sub] using hh
  have hqp : q ≤ 2 * p + 8 := by
    have hh : q ≤ ∑ i : Fin 4, (2 * (R * (u i - v i)) ^ 2 + 2) := by
      apply Finset.sum_le_sum
      intro i _
      have h := abs_sub_floor_sub_le_one (R * u i) (R * v i)
      have hh' := (abs_le.mp h)
      push_cast at hh' ⊢
      nlinarith [sq_nonneg (2 * R * (u i - v i) -
        ((⌊R * u i⌋ : ℝ) - (⌊R * v i⌋ : ℝ)))]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] at hh
    norm_num at hh
    exact hh
  have hp : p = R ^ 2 * ‖u - v‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [PiLp.sub_apply]
    ring
  have hq : 0 ≤ q := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hR2 : 1 ≤ R ^ 2 := by nlinarith
  have hRpos : 0 < R ^ 2 := by positivity
  constructor
  · apply (le_div_iff₀ hRpos).2
    rw [hp] at hpq
    nlinarith
  · apply (div_le_iff₀ hRpos).2
    rw [hp] at hqp
    nlinarith

end Sandpile.Support
