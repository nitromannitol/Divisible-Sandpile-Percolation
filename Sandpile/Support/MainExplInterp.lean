import Sandpile.Support.ExplInterp
import Sandpile.Support.LinStationary

/-!
# Measurability and mesh-point control of the multilinear interpolation

The multilinear interpolation of a measurable lattice field is measurable, and it
differs from the value at the mesh point of the cell by at most the oscillation of
the field over that cell. Both are used to pass from the lattice value at
`⌊Rx⌋`, which the coupling controls, to the interpolation at `x`, which is the
field of `thm:main-explosion`(i)(b).
-/

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.Continuum

variable {d : ℕ}

/-- The multilinear interpolation of a measurable lattice field is measurable. -/
theorem measurable_multilinearInterp (R : ℝ) (f : Site d → ℝ) (hf : Measurable f) :
    Measurable (fun z : Space d => multilinearInterp R f z) := by
  unfold Sandpile.Continuum.multilinearInterp
  apply Finset.measurable_sum
  intro ε hε
  apply Measurable.mul
  · apply Finset.measurable_prod
    intro i hi
    split_ifs with h
    · fun_prop
    · fun_prop
  · apply hf.comp
    apply measurable_pi_iff.mpr
    intro i
    split_ifs with h
    · fun_prop
    · fun_prop

/-- The interpolation at `z` differs from the value at the mesh point `⌊Rz⌋` by at
most the oscillation of the field over the cell. -/
theorem abs_multilinearInterp_sub_mesh_le (R : ℝ) (f : Site d → ℝ) (z : Space d) (M : ℝ)
    (hf : ∀ x : Site d, |f x - f (fun i => ⌊R * z i⌋)| ≤ M) :
    |multilinearInterp R f z - f (fun i => ⌊R * z i⌋)| ≤ M := by
  have h := Sandpile.Continuum.abs_multilinearInterp_le R
    (fun x => f x - f (fun i => ⌊R * z.ofLp i⌋)) z M hf
  simpa only [Sandpile.Continuum.multilinearInterp_sub, Sandpile.Continuum.multilinearInterp_const,
    sub_self, sub_zero] using h

/-- The multilinear interpolation, read at a fixed point, is measurable in the
lattice field. -/
theorem measurable_multilinearInterp_apply {Ω : Type*} [MeasurableSpace Ω]
    (R : ℝ) (f : Ω → Site d → ℝ) (z : Space d) (hf : Measurable f) :
    Measurable fun ω => multilinearInterp R (f ω) z := by
  unfold Sandpile.Continuum.multilinearInterp
  apply Finset.measurable_sum
  intro ε hε
  apply Measurable.mul
  · fun_prop
  · fun_prop

end Sandpile.Continuum

namespace Sandpile

variable {d : ℕ}

/-- The rescaled odometer field is measurable in the scenery. -/
theorem measurable_rescaled_odometer_field (T : ℝ) (R : ℝ) :
    Measurable fun σ : Sandpile.Site d → ℝ => fun y : Sandpile.Site d =>
      R ^ (-(2 - (d : ℝ) / 2)) * Sandpile.odometer σ ⌊T * R ^ 2⌋₊ y := by
  refine measurable_pi_iff.mpr fun y => ?_
  exact (Sandpile.measurable_odometer ⌊T * R ^ 2⌋₊ y).const_mul _

end Sandpile
