import Sandpile.Support.LinJacobianCell

/-!
# The cell `L²` bound for a general test function

`eq:dgt4-tested-cell-l2` (`sandpile.tex:5699-5702`) for a test function that is only
bounded, integrable and square integrable with compact support.

`Support/LinCellL2.lean` proves the display for a smooth compactly supported test
function, but the only facts it uses are that the function and its square are
integrable. The linearization for a SIGNED test function is obtained by splitting it into
its positive and negative parts, which are no longer smooth, so the display is restated
here with those two integrabilities as hypotheses.
-/

open MeasureTheory Filter Topology
open Sandpile.Continuum

namespace Sandpile

variable {d : ℕ}

/-- Cauchy-Schwarz on one cell of the mesh: the squared cell mass of a bounded and square
integrable `φ` is at most `R⁻¹ᵈ` times the integral of `φ²` over the cell, via
`sq_setIntegral_le` and the cell's finite volume `R⁻¹ᵈ`. -/
theorem sq_cellMass_le' {R : ℝ} (hR : 0 < R) {φ : Space d → ℝ}
    (hint : Integrable φ) (hint2 : Integrable (fun z => φ z ^ 2)) (x : Sandpile.Site d) :
    (Sandpile.Support.cellMass R φ x) ^ 2
      ≤ R⁻¹ ^ d * ∫ z in Sandpile.Support.cell d R x, φ z ^ 2 := by
  have hfin : (volume : Measure (Space d)) (Sandpile.Support.cell d R x) ≠ ⊤ := by
    rw [Sandpile.Support.volume_cell d hR x]
    exact (ENNReal.pow_lt_top ENNReal.ofReal_lt_top).ne
  have h := sq_setIntegral_le (volume : Measure (Space d)) (Sandpile.Support.cell d R x) φ
    hint.integrableOn hint2.integrableOn hfin
  rwa [measureReal_cell hR x] at h

/-- Summing `sq_cellMass_le'` over a finite set of cell centres: since the cells indexed by
`s` are pairwise disjoint (`Sandpile.Support.cell_disjoint`), the sum of the squared cell
masses is at most `R⁻¹ᵈ` times the integral of `φ²` over the whole space. -/
theorem sum_sq_cellMass_le' {R : ℝ} (hR : 0 < R) {φ : Space d → ℝ}
    (hint : Integrable φ) (hint2 : Integrable (fun z => φ z ^ 2))
    (s : Finset (Sandpile.Site d)) :
    ∑ x ∈ s, (Sandpile.Support.cellMass R φ x) ^ 2
      ≤ R⁻¹ ^ d * ∫ z, φ z ^ 2 ∂(volume : Measure (Space d)) := by
  have hstep : ∑ x ∈ s, (Sandpile.Support.cellMass R φ x) ^ 2
      ≤ ∑ x ∈ s, R⁻¹ ^ d * ∫ z in Sandpile.Support.cell d R x, φ z ^ 2 :=
    Finset.sum_le_sum fun x _ => sq_cellMass_le' hR hint hint2 x
  refine le_trans hstep ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hunion : ∫ z in ⋃ x ∈ s, Sandpile.Support.cell d R x, φ z ^ 2
      ∂(volume : Measure (Space d))
      = ∑ x ∈ s, ∫ z in Sandpile.Support.cell d R x, φ z ^ 2
        ∂(volume : Measure (Space d)) :=
    integral_biUnion_finset s (fun x _ => Sandpile.Support.measurableSet_cell d R x)
      (fun x _ y _ hxy => Sandpile.Support.cell_disjoint hxy)
      (fun x _ => hint2.integrableOn)
  rw [← hunion]
  exact setIntegral_le_integral hint2 (Filter.Eventually.of_forall fun z => sq_nonneg _)

/-- The `sum_sq_cellMass_le'` bound rescaled by `R^{(d-4)/2}`, the tested weight's own
scale factor: the rescaled sum of squared cell masses is at most `(∫ φ²) · R⁻⁴`, computed
by absorbing the rescaling power into the `R⁻¹ᵈ` factor via `Real.rpow` arithmetic. -/
theorem sum_sq_scaled_cellMass_le' {R : ℝ} (hR : 0 < R) {φ : Space d → ℝ}
    (hint : Integrable φ) (hint2 : Integrable (fun z => φ z ^ 2))
    (s : Finset (Sandpile.Site d)) :
    ∑ x ∈ s, (R ^ (((d : ℝ) - 4) / 2) * Sandpile.Support.cellMass R φ x) ^ 2
      ≤ (∫ z, φ z ^ 2 ∂(volume : Measure (Space d))) * R ^ (-(4 : ℝ)) := by
  have hpow : (R ^ (((d : ℝ) - 4) / 2)) ^ 2 = R ^ ((d : ℝ) - 4) := by
    rw [← Real.rpow_natCast (R ^ (((d : ℝ) - 4) / 2)) 2, ← Real.rpow_mul hR.le]
    norm_num
  have hinv : (R⁻¹ : ℝ) ^ d = R ^ (-(d : ℝ)) := by
    rw [Real.rpow_neg hR.le, Real.rpow_natCast R d, inv_pow]
  have hmul : R ^ ((d : ℝ) - 4) * R ^ (-(d : ℝ)) = R ^ (-(4 : ℝ)) := by
    rw [← Real.rpow_add hR]
    ring_nf
  calc ∑ x ∈ s, (R ^ (((d : ℝ) - 4) / 2) * Sandpile.Support.cellMass R φ x) ^ 2
      = (R ^ (((d : ℝ) - 4) / 2)) ^ 2 * ∑ x ∈ s, (Sandpile.Support.cellMass R φ x) ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by ring
    _ ≤ (R ^ (((d : ℝ) - 4) / 2)) ^ 2 *
          (R⁻¹ ^ d * ∫ z, φ z ^ 2 ∂(volume : Measure (Space d))) :=
        mul_le_mul_of_nonneg_left (sum_sq_cellMass_le' hR hint hint2 s) (by positivity)
    _ = (∫ z, φ z ^ 2 ∂(volume : Measure (Space d))) * R ^ (-(4 : ℝ)) := by
        rw [hpow, hinv, ← mul_assoc, hmul, mul_comm]

/-- **`eq:dgt4-tested-cell-l2`** over the whole lattice, for a bounded,
integrable and square integrable test function. -/
theorem tsum_sq_testedWeight_le' {R : ℝ} (hR : 0 < R) (L : ℝ) {φ : Space d → ℝ}
    (hint : Integrable φ) (hint2 : Integrable (fun z => φ z ^ 2)) :
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
  refine (sum_sq_scaled_cellMass_le' hR hint hint2 _).trans (le_of_eq ?_)
  congr 1
  rw [Real.rpow_neg hR.le, ← Real.rpow_natCast R 4]
  norm_num

end Sandpile
