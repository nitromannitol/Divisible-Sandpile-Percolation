/-
The tested weight `a_R(x) = R^{(d-4)/2}φ_R(x)` of `lem:dgt4-linearization-from-survival`
(`sandpile.tex:5663-5666`) as a function on the whole lattice, and
`eq:dgt4-tested-cell-l2` (`sandpile.tex:5699-5702`) for it:

  `∑_{x∈Z^d} a_R(x)^2 ≤ C(φ)R^{-4}`.

The weight is carried by the finitely many cells the test function meets, so the
sum over the lattice is the finite sum of `Support/LinCellL2.lean`.
-/
import Sandpile.Support.LinCellL2
import Sandpile.Support.LinTested

open MeasureTheory Filter Topology
open Sandpile.Continuum

namespace Sandpile

variable {d : ℕ}

/-- The tested weight `a_R(x) = R^{(d-4)/2}φ_R(x)`, carried by the cells the test
function meets. -/
noncomputable def testedWeight (d : ℕ) (R L : ℝ) (φ : Space d → ℝ) (x : Site d) : ℝ :=
  if x ∈ Sandpile.Support.supportBox d R L then
    R ^ (((d : ℝ) - 4) / 2) * Sandpile.Support.cellMass R φ x else 0

theorem testedWeight_eq_zero_of_notMem (R L : ℝ) (φ : Space d → ℝ) {x : Site d}
    (hx : x ∉ Sandpile.Support.supportBox d R L) : testedWeight d R L φ x = 0 := by
  rw [testedWeight, if_neg hx]

theorem testedWeight_nonneg {R : ℝ} (hR : 0 < R) (L : ℝ) {φ : Space d → ℝ}
    (hφ : ∀ z, 0 ≤ φ z) (x : Site d) : 0 ≤ testedWeight d R L φ x := by
  rw [testedWeight]
  split
  · exact mul_nonneg (Real.rpow_nonneg hR.le _)
      (integral_nonneg fun z => hφ z)
  · exact le_refl 0

theorem summable_sq_testedWeight (R L : ℝ) (φ : Space d → ℝ) :
    Summable fun x : Site d => (testedWeight d R L φ x) ^ 2 := by
  classical
  refine summable_of_ne_finset_zero (s := Sandpile.Support.supportBox d R L) fun x hx => ?_
  rw [testedWeight_eq_zero_of_notMem R L φ hx]
  norm_num

/-- **`eq:dgt4-tested-cell-l2`** (`sandpile.tex:5694-5697`) over the whole
lattice: `∑_x a_R(x)^2 ≤ C(φ)R^{-4}`. -/
theorem tsum_sq_testedWeight_le {R : ℝ} (hR : 0 < R) (L : ℝ) {φ : Space d → ℝ}
    (hφ : Sandpile.Continuum.IsTestFn Set.univ φ) :
    (∑' x : Site d, (testedWeight d R L φ x) ^ 2)
      ≤ (∫ z, φ z ^ 2 ∂(volume : Measure (Space d))) * (R ^ 4)⁻¹ := by
  classical
  have hzero : ∀ x ∉ Sandpile.Support.supportBox d R L, (testedWeight d R L φ x) ^ 2 = 0 := by
    intro x hx
    rw [testedWeight_eq_zero_of_notMem R L φ hx]
    norm_num
  rw [tsum_eq_sum hzero]
  have hfin : ∑ x ∈ Sandpile.Support.supportBox d R L, (testedWeight d R L φ x) ^ 2
      = ∑ x ∈ Sandpile.Support.supportBox d R L,
          (R ^ (((d : ℝ) - 4) / 2) * Sandpile.Support.cellMass R φ x) ^ 2 :=
    Finset.sum_congr rfl fun x hx => by rw [testedWeight, if_pos hx]
  rw [hfin]
  refine (sum_sq_scaled_cellMass_le hR hφ _).trans (le_of_eq ?_)
  congr 1
  rw [Real.rpow_neg hR.le, ← Real.rpow_natCast R 4]
  norm_num

end Sandpile
