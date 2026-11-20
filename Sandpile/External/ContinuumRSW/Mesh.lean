import Sandpile.External.ContinuumRSW.GridClipping

/-!
# Mesh arithmetic for continuum crossings

A square mesh aligns the fixed short side and rounds the long side up by at
most one mesh length.
-/

open Filter Topology

namespace Sandpile.External.ContinuumRSW

/-- Mesh size for the `n`th approximation at scale `R`. -/
noncomputable def crossingMesh (R : ℝ) (n : ℕ) : ℝ := R / ((n : ℝ) + 1)

/-- The lattice width whose right face first reaches the desired aspect ratio. -/
noncomputable def crossingMeshWidth (ρ : ℝ) (n : ℕ) : ℕ :=
  ⌈2 * ρ * ((n : ℝ) + 1)⌉₊

/-- The mesh tends to zero. -/
theorem tendsto_crossingMesh (R : ℝ) : Tendsto (crossingMesh R) atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => R / ((n : ℝ) + 1)) atTop (𝓝 0)
  simpa only [div_eq_mul_inv, one_div, one_mul, mul_zero] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul R

/-- The short side of the sampled rectangles is exactly `2R`. -/
theorem crossingMesh_short_side (R : ℝ) (n : ℕ) :
    crossingMesh R n * (2 * (n + 1) : ℕ) = 2 * R := by
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  simp only [crossingMesh, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
  field_simp

/-- The long side of an integer-aspect sampled rectangle is exact. -/
theorem crossingMesh_long_side (R : ℝ) (M n : ℕ) :
    crossingMesh R n * (2 * M * (n + 1) : ℕ) = 2 * M * R := by
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  simp only [crossingMesh, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
  field_simp

/-- The rounded lattice face lies between the desired real face and one mesh beyond it. -/
theorem crossingMeshWidth_bounds {R ρ : ℝ} (hR : 0 < R) (hρ : 0 ≤ ρ) (n : ℕ) :
    2 * ρ * R ≤ crossingMesh R n * (crossingMeshWidth ρ n : ℝ) ∧
      crossingMesh R n * (crossingMeshWidth ρ n : ℝ) ≤ 2 * ρ * R + crossingMesh R n := by
  have ht : 0 < crossingMesh R n := by simp only [crossingMesh]; positivity
  have hle := Nat.le_ceil (2 * ρ * ((n : ℝ) + 1))
  have hlt := Nat.ceil_lt_add_one (show 0 ≤ 2 * ρ * ((n : ℝ) + 1) by positivity)
  have halign : crossingMesh R n * (2 * ρ * ((n : ℝ) + 1)) = 2 * ρ * R := by
    have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
    simp only [crossingMesh]
    field_simp
  constructor
  · rw [← halign]
    exact mul_le_mul_of_nonneg_left hle ht.le
  · calc
      crossingMesh R n * (crossingMeshWidth ρ n : ℝ) ≤
          crossingMesh R n * (2 * ρ * ((n : ℝ) + 1) + 1) :=
        mul_le_mul_of_nonneg_left hlt.le ht.le
      _ = 2 * ρ * R + crossingMesh R n := by rw [mul_add, halign, mul_one]

/-- If `M` dominates the real aspect ratio, the rounded face lies within the
integer-aspect rectangle. -/
theorem crossingMeshWidth_le {ρ : ℝ} {M : ℕ} (hρM : ρ ≤ M) (n : ℕ) :
    crossingMeshWidth ρ n ≤ 2 * M * (n + 1) := by
  apply Nat.ceil_le.mpr
  push_cast
  have hn : 0 ≤ (n : ℝ) + 1 := by positivity
  nlinarith

end Sandpile.External.ContinuumRSW
