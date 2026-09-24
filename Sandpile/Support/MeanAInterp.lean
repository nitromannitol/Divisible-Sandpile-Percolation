/-
The rescaled odometer of `cor:dlt4-mean-asymptotic` is the interpolated field of
`thm:main-explosion`(i)(b) read at a mesh point.

`sandpile.tex:1817-1821` defines `𝒰_R(T,x) = R^{-(2-d/2)}u_{⌊R²T⌋}(⌊Rx⌋)`, a value
at a LATTICE site, while part (i)(b) (`sandpile.tex:217-235`) is stated for the
multilinear interpolation of the same lattice field, evaluated at a point of `ℝ^d`.
The paper reconciles the two in one sentence at `sandpile.tex:1821-1824`: "The
standard interpolation from the parabolic mesh has the same compact-uniform limit,
because the limiting field is uniformly continuous on compact subsets".  The first
half of that reconciliation is exact and is proved here: at the mesh point
`⌊Rx⌋/R` the interpolation returns the lattice value, so

  `𝒰_R(T,x) = F_R(meshPoint R x)`,   `F_R(z) = multilinearInterp R (R^{-(2-d/2)}u_{⌊TR²⌋}) z`.

At `x = 0` the mesh point IS `x`, so at the origin the two fields agree on the nose
and no approximation is needed at all.  For `x ≠ 0` what remains is
`‖meshPoint R x - x‖ ≤ √d/R` (`Sandpile.Support.norm_meshPoint_sub_le`) fed into the
modulus-of-continuity half of the tightness clause of (i)(b).
-/
import Sandpile.Support.ContMeshPoint
import Sandpile.Support.ExplInterp
import Sandpile.Support.MeanAValue

open MeasureTheory Filter Topology

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

variable {d : ℕ}

/-- At a mesh point the scaled coordinate is an integer. -/
theorem fract_mul_meshPoint (R : ℝ) (hR : R ≠ 0) (x : Space d) (i : Fin d) :
    Int.fract (R * meshPoint R x i) = 0 := by
  rw [meshPoint_apply, mul_div_cancel₀ _ hR]
  exact Int.fract_intCast _

/-- At a mesh point the scaled coordinate has the original floor. -/
theorem floor_mul_meshPoint (R : ℝ) (hR : R ≠ 0) (x : Space d) (i : Fin d) :
    ⌊R * meshPoint R x i⌋ = ⌊R * x i⌋ := by
  rw [meshPoint_apply, mul_div_cancel₀ _ hR]
  exact Int.floor_intCast _

/-- **The interpolated field at the mesh point is the lattice value.** -/
theorem multilinearInterp_meshPoint (R : ℝ) (hR : R ≠ 0) (f : Site d → ℝ) (x : Space d) :
    multilinearInterp R f (meshPoint R x) = f fun i => ⌊R * x i⌋ := by
  rw [multilinearInterp_of_fract_eq_zero R f (meshPoint R x) (fun i => fract_mul_meshPoint R hR x i)]
  congr 1
  funext i
  exact floor_mul_meshPoint R hR x i

/-- **The rescaled odometer is the interpolated field of part (i)(b), read at the mesh
point of `x`.**  This is the exact half of `sandpile.tex:1821-1824`. -/
theorem rescaledOdometer_eq_multilinearInterp (d : ℕ) (R T : ℝ) (hR : R ≠ 0)
    (x : Space d) (σ : Site d → ℝ) :
    Sandpile.Continuum.rescaledOdometer d R T x σ
      = multilinearInterp R
          (fun y => R ^ (-(2 - (d : ℝ) / 2)) * Sandpile.odometer σ ⌊T * R ^ 2⌋₊ y)
          (meshPoint R x) := by
  rw [multilinearInterp_meshPoint R hR _ x]
  unfold Sandpile.Continuum.rescaledOdometer
  rw [mul_comm (R ^ 2) T]

/-- **At the origin the mesh point is the origin**, so there the rescaled odometer is
the interpolated field at `x` itself and no approximation enters. -/
theorem meshPoint_zero (R : ℝ) : meshPoint R (0 : Space d) = 0 := by
  ext i
  rw [meshPoint_apply]
  simp

/-- The rescaled odometer at the origin, as the interpolated field at the origin. -/
theorem rescaledOdometer_zero_eq_multilinearInterp (d : ℕ) (R T : ℝ) (hR : R ≠ 0)
    (σ : Site d → ℝ) :
    Sandpile.Continuum.rescaledOdometer d R T 0 σ
      = multilinearInterp R
          (fun y => R ^ (-(2 - (d : ℝ) / 2)) * Sandpile.odometer σ ⌊T * R ^ 2⌋₊ y)
          (0 : Space d) := by
  rw [rescaledOdometer_eq_multilinearInterp d R T hR 0 σ, meshPoint_zero]

end Sandpile.Support
