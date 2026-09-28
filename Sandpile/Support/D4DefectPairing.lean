import Sandpile.Support.D4DefectParity

/-!
# The Cauchy-Schwarz pairing bound for the dimension-four defect

The pairing step of Step 1 of `prop:d4-superdiffusive-limit`.

The `ω`-representative pairs a lattice kernel against the cell masses
`m_R(x) = ∫_{R^{-1}(x+[0,1)^4)}φ̃` of `Sandpile.Support.latticePairing_eq_sum`,
so the defect at a site `y` is the finite sum `∑_x K(x,y)m_R(x)`.  Cauchy-Schwarz
in `x` against the weights `|m_R(x)|` turns a uniform `ℓ²` bound on the slices
`K(x,·)` into an `ℓ²` bound on the pairing, with the total mass `∑_x|m_R(x)|`
squared in front.  Nothing here is analytic: the cell decomposition has already
made the pairing a finite sum. The single theorem `tsum_sq_finset_pairing_le` proves this
Cauchy-Schwarz pairing bound.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Sandpile

variable {d : ℕ}

/-- **The pairing bound.**  If every slice `K(x,·)` with `x` in `s` has `ℓ²` norm
squared at most `B`, and the weights have total mass at most `M`, then the
paired family `y ↦ ∑_{x∈s}K(x,y)m(x)` has `ℓ²` norm squared at most `M²B`. -/
theorem tsum_sq_finset_pairing_le {ι : Type*} (s : Finset ι) (m : ι → ℝ)
    (K : ι → Site d → ℝ) {M B : ℝ} (hM0 : 0 ≤ M) (hM : ∑ x ∈ s, |m x| ≤ M)
    (hB0 : 0 ≤ B)
    (hB : ∀ x ∈ s, ∑' y : Site d, ENNReal.ofReal (K x y ^ 2) ≤ ENNReal.ofReal B) :
    ∑' y : Site d, ENNReal.ofReal ((∑ x ∈ s, K x y * m x) ^ 2) ≤
      ENNReal.ofReal (M * M * B) := by
  -- Cauchy-Schwarz in the cell index, at the weights `|m x|`
  have hptw : ∀ y : Site d, (∑ x ∈ s, K x y * m x) ^ 2 ≤
      M * ∑ x ∈ s, |m x| * K x y ^ 2 := by
    intro y
    have habs : |∑ x ∈ s, K x y * m x| ≤
        ∑ x ∈ s, Real.sqrt |m x| * (|K x y| * Real.sqrt |m x|) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq ?_)
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [abs_mul]
      have hsq : Real.sqrt |m x| * Real.sqrt |m x| = |m x| :=
        Real.mul_self_sqrt (abs_nonneg _)
      calc |K x y| * |m x| = |K x y| * (Real.sqrt |m x| * Real.sqrt |m x|) := by rw [hsq]
        _ = Real.sqrt |m x| * (|K x y| * Real.sqrt |m x|) := by ring
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun x => Real.sqrt |m x|)
      (fun x => |K x y| * Real.sqrt |m x|)
    have h1 : ∑ x ∈ s, Real.sqrt |m x| ^ 2 = ∑ x ∈ s, |m x| :=
      Finset.sum_congr rfl fun x _ => Real.sq_sqrt (abs_nonneg _)
    have h2 : ∑ x ∈ s, (|K x y| * Real.sqrt |m x|) ^ 2 = ∑ x ∈ s, |m x| * K x y ^ 2 := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [mul_pow, Real.sq_sqrt (abs_nonneg _), sq_abs]
      ring
    rw [h1, h2] at hcs
    have hsqle : (∑ x ∈ s, K x y * m x) ^ 2 ≤
        (∑ x ∈ s, Real.sqrt |m x| * (|K x y| * Real.sqrt |m x|)) ^ 2 := by
      rw [← sq_abs (∑ x ∈ s, K x y * m x)]
      exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    have hnn : (0 : ℝ) ≤ ∑ x ∈ s, |m x| * K x y ^ 2 :=
      Finset.sum_nonneg fun x _ => mul_nonneg (abs_nonneg _) (sq_nonneg _)
    have hms : (0 : ℝ) ≤ ∑ x ∈ s, |m x| := Finset.sum_nonneg fun x _ => abs_nonneg _
    calc (∑ x ∈ s, K x y * m x) ^ 2
        ≤ (∑ x ∈ s, Real.sqrt |m x| * (|K x y| * Real.sqrt |m x|)) ^ 2 := hsqle
      _ ≤ (∑ x ∈ s, |m x|) * ∑ x ∈ s, |m x| * K x y ^ 2 := hcs
      _ ≤ M * ∑ x ∈ s, |m x| * K x y ^ 2 := mul_le_mul_of_nonneg_right hM hnn
  -- sum the pointwise bound over the lattice, in `ℝ≥0∞`
  have hstep : ∀ y : Site d, ENNReal.ofReal ((∑ x ∈ s, K x y * m x) ^ 2) ≤
      ENNReal.ofReal M * ∑ x ∈ s, ENNReal.ofReal (|m x| * K x y ^ 2) := by
    intro y
    refine le_trans (ENNReal.ofReal_le_ofReal (hptw y)) ?_
    rw [ENNReal.ofReal_mul hM0]
    refine mul_le_mul_right (le_of_eq ?_) _
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))]
  calc ∑' y : Site d, ENNReal.ofReal ((∑ x ∈ s, K x y * m x) ^ 2)
      ≤ ∑' y : Site d, ENNReal.ofReal M * ∑ x ∈ s, ENNReal.ofReal (|m x| * K x y ^ 2) :=
        ENNReal.tsum_le_tsum hstep
    _ = ENNReal.ofReal M * ∑ x ∈ s, ∑' y : Site d, ENNReal.ofReal (|m x| * K x y ^ 2) := by
        rw [ENNReal.tsum_mul_left,
          Summable.tsum_finsetSum (fun x (_ : x ∈ s) => ENNReal.summable)]
    _ ≤ ENNReal.ofReal M * ∑ x ∈ s, ENNReal.ofReal |m x| * ENNReal.ofReal B := by
        refine mul_le_mul_right (Finset.sum_le_sum fun x hx => ?_) _
        have hfac : ∀ y : Site d, ENNReal.ofReal (|m x| * K x y ^ 2) =
            ENNReal.ofReal |m x| * ENNReal.ofReal (K x y ^ 2) :=
          fun y => ENNReal.ofReal_mul (abs_nonneg _)
        rw [tsum_congr hfac, ENNReal.tsum_mul_left]
        exact mul_le_mul_right (hB x hx) _
    _ = ENNReal.ofReal M * ENNReal.ofReal B * ∑ x ∈ s, ENNReal.ofReal |m x| := by
        rw [← Finset.sum_mul]
        ring
    _ ≤ ENNReal.ofReal M * ENNReal.ofReal B * ENNReal.ofReal M := by
        refine mul_le_mul_right ?_ _
        rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => abs_nonneg _)]
        exact ENNReal.ofReal_le_ofReal hM
    _ = ENNReal.ofReal (M * M * B) := by
        rw [← ENNReal.ofReal_mul hM0, ← ENNReal.ofReal_mul (mul_nonneg hM0 hB0)]
        congr 1
        ring

end Sandpile
