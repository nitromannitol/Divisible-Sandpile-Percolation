import Sandpile.External.Stopping.CubeStoppedPathLimit
import Sandpile.External.Stopping.WalkInterpolation
import Sandpile.Frozen.MeanLocalization

/-!
# Geometry of rescaled lattice cubes

After centering at the lattice cube center and scaling by its radius, vertices
inside the lattice cube lie in the closed unit cube, while vertices outside the
lattice cube lie outside the open unit cube.
-/

open Set

namespace Sandpile.External.Stopping

/-- A lattice site rescaled relative to a lattice center. -/
noncomputable def centeredScaledSite {d : ℕ} (R : ℝ) (q v : Site d) : Continuum.Space d :=
  Lclt.scaledSite R (v - q)

/-- A vertex of a lattice cube rescales into the closed unit cube. -/
theorem centeredScaledSite_mem_closedUnitCube {d : ℕ} {R : ℝ} (hR : 0 < R)
    {q v : Site d} (hv : v ∈ supBox q R) :
    centeredScaledSite R q v ∈ closedUnitCube (0 : Continuum.Space d) := by
  intro i
  have hi : |v i - q i| ≤ ⌊R⌋ := hv i
  have hir : ((|v i - q i| : ℤ) : ℝ) ≤ (⌊R⌋ : ℝ) := by exact_mod_cast hi
  have hfloor : (⌊R⌋ : ℝ) ≤ R := Int.floor_le R
  change |((v i - q i : ℤ) : ℝ) / R - 0| ≤ 1
  rw [sub_zero, abs_div, abs_of_pos hR, ← Int.cast_abs]
  exact (div_le_one hR).2 (hir.trans hfloor)

/-- A vertex outside a lattice cube rescales outside the open unit cube. -/
theorem centeredScaledSite_not_mem_openUnitCube {d : ℕ} {R : ℝ} (hR : 0 < R)
    {q v : Site d} (hv : v ∉ supBox q R) :
    centeredScaledSite R q v ∉ openUnitCube (0 : Continuum.Space d) := by
  have hi : ∃ i, ⌊R⌋ < |v i - q i| := by
    simpa only [supBox, mem_ofPred_eq, not_forall, not_le] using hv
  obtain ⟨i, hi⟩ := hi
  have hi' : ⌊R⌋ + 1 ≤ |v i - q i| := by omega
  have hir : ((⌊R⌋ : ℤ) : ℝ) + 1 ≤ ((|v i - q i| : ℤ) : ℝ) := by exact_mod_cast hi'
  have hfloor : R < (⌊R⌋ : ℝ) + 1 := Int.lt_floor_add_one R
  intro h
  have hc := h i
  change |((v i - q i : ℤ) : ℝ) / R - 0| < 1 at hc
  rw [sub_zero, abs_div, abs_of_pos hR, ← Int.cast_abs] at hc
  have hc' : ((|v i - q i| : ℤ) : ℝ) < R := (div_lt_one hR).1 hc
  linarith

end Sandpile.External.Stopping
