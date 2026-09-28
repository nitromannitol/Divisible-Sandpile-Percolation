import Sandpile.Support.ContCell

/-!
# The parity imbalance of the mesh

The parity imbalance of the mesh, for the second display of Step 2 of
`prop:d4-superdiffusive-limit` (`sandpile.tex:3374-3382`).

The paper compares the smoothed error with the field `C_R` that is constant on each parity class
of the lattice. Such a field pairs against the `ω`-shifted test function through the difference
of its two constants times the mass the shift puts on ONE parity class, the total mass being
zero. That mass is small because the parity of the cell `⌊Rz⌋` FLIPS under the translation by
`e_i/R` (`parityChar_add_meshStep`): pairing the shift with the parity indicator (`parityChar`)
and translating by one step turns twice the imbalance into the integral of the increment of the
shift over one step (`abs_integral_mul_parityChar_le`). This is the paper's "cancellation
between the two parity classes", and it reduces the second display to a modulus of continuity
at scale `1/R`.
-/

open MeasureTheory Filter Topology
namespace Sandpile.Support
open Sandpile.Continuum

variable {d : ℕ}

/-- The even-parity indicator of the mesh cell of `z`. -/
noncomputable def parityChar (R : ℝ) (z : Space d) : ℝ :=
  if Even (∑ i : Fin d, ((fun i => ⌊R * z i⌋) i - (0 : Sandpile.Site d) i)) then 1 else 0

/-- The step `e_{i₀}/R` of the mesh. -/
noncomputable def meshStep (d : ℕ) (R : ℝ) (i₀ : Fin d) : Space d :=
  (EuclideanSpace.single i₀ (R⁻¹ : ℝ))

/-- The `i`-th coordinate of `meshStep d R i₀` is `R⁻¹` at `i = i₀` and `0` elsewhere. -/
theorem meshStep_apply {R : ℝ} (i₀ i : Fin d) :
    meshStep d R i₀ i = if i = i₀ then R⁻¹ else 0 := by
  simp [meshStep]

/-- **The parity of the cell flips under the mesh step.** -/
theorem parityChar_add_meshStep {R : ℝ} (hR : 0 < R) (i₀ : Fin d) (z : Space d) :
    parityChar R z + parityChar R (z + meshStep d R i₀) = 1 := by
  classical
  have hcoord : ∀ i : Fin d, ⌊R * ((z + meshStep d R i₀) i)⌋ =
      ⌊R * z i⌋ + (if i = i₀ then 1 else 0) := by
    intro i
    have hadd : (z + meshStep d R i₀) i = z i + (if i = i₀ then R⁻¹ else 0) := by
      rw [← meshStep_apply i₀ i]
      rfl
    rw [hadd, mul_add]
    by_cases hi : i = i₀
    · rw [if_pos hi, if_pos hi, mul_inv_cancel₀ (ne_of_gt hR), Int.floor_add_one]
    · rw [if_neg hi, if_neg hi, mul_zero, add_zero, add_zero]
  have hsum : ∑ i : Fin d, ⌊R * ((z + meshStep d R i₀) i)⌋ = (∑ i : Fin d, ⌊R * z i⌋) + 1 := by
    simp_rw [hcoord]
    rw [Finset.sum_add_distrib]
    congr 1
    simp
  unfold parityChar
  simp only [Pi.zero_apply, sub_zero]
  rw [hsum]
  by_cases hev : Even (∑ i : Fin d, ⌊R * z i⌋)
  · rw [if_pos hev, if_neg (by simpa [Int.even_add_one] using hev)]
    norm_num
  · rw [if_neg hev, if_pos (by simpa [Int.even_add_one] using hev)]
    norm_num

/-- The parity indicator of the mesh is measurable and bounded by one. -/
theorem measurable_parityChar (R : ℝ) : Measurable (parityChar (d := d) R) := by
  classical
  have hf : Measurable (fun z : Space d => ∑ i : Fin d, ⌊R * z i⌋) :=
    Finset.measurable_sum _ fun i _ => measurable_coord R i
  have hset : MeasurableSet {z : Space d | Even (∑ i : Fin d, ⌊R * z i⌋)} := by
    have : {z : Space d | Even (∑ i : Fin d, ⌊R * z i⌋)} =
        (fun z : Space d => ∑ i : Fin d, ⌊R * z i⌋) ⁻¹' {n : ℤ | Even n} := rfl
    rw [this]
    exact hf MeasurableSet.of_discrete
  have hcongr : parityChar (d := d) R =
      fun z => if Even (∑ i : Fin d, ⌊R * z i⌋) then (1:ℝ) else 0 := by
    funext z
    simp [parityChar]
  rw [hcongr]
  exact measurable_const.ite hset measurable_const

/-- `parityChar` only ever takes the values `0` and `1`, so it is nonnegative. -/
theorem parityChar_nonneg (R : ℝ) (z : Space d) : 0 ≤ parityChar R z := by
  unfold parityChar; split <;> norm_num

/-- `parityChar` only ever takes the values `0` and `1`, so it is at most `1`. -/
theorem parityChar_le_one (R : ℝ) (z : Space d) : parityChar R z ≤ 1 := by
  unfold parityChar; split <;> norm_num

/-- **The parity imbalance of a mean-zero function is a modulus of continuity.**
Because the parity of the cell flips under the mesh step and the function has
total mass zero, twice the mass it puts on the even cells is the pairing of its
increment over one step against the parity indicator. -/
theorem abs_integral_mul_parityChar_le {R : ℝ} (hR : 0 < R) (i₀ : Fin d) (ψ : Space d → ℝ)
    (hint : Integrable ψ) (hmean : ∫ z : Space d, ψ z = 0) :
    |∫ z : Space d, ψ z * parityChar R z| ≤
      (1/2) * ∫ z : Space d, |ψ z - ψ (z + meshStep d R i₀)| := by
  classical
  set h : Space d := meshStep d R i₀ with hh
  have hmχ : Measurable (parityChar (d := d) R) := measurable_parityChar R
  have hbound : ∀ᵐ z : Space d, ‖parityChar R z‖ ≤ 1 := by
    refine Filter.Eventually.of_forall fun z => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (parityChar_nonneg R z)]
    exact parityChar_le_one R z
  have hintT : Integrable (fun z : Space d => ψ (z + h)) :=
    (measurePreserving_add_right volume h).integrable_comp hint.aestronglyMeasurable |>.mpr hint
  have hintψχ : Integrable (fun z : Space d => ψ z * parityChar R z) :=
    hint.mul_bdd hmχ.aestronglyMeasurable hbound
  have hintTχ : Integrable (fun z : Space d => ψ (z + h) * parityChar R z) :=
    hintT.mul_bdd hmχ.aestronglyMeasurable hbound
  -- the translated pairing
  have hshift : ∫ z : Space d, ψ z * parityChar R z =
      ∫ z : Space d, ψ (z + h) * parityChar R (z + h) :=
    (integral_add_right_eq_self (fun z : Space d => ψ z * parityChar R z) h).symm
  have hflip : ∀ z : Space d, parityChar R (z + h) = 1 - parityChar R z := by
    intro z
    have := parityChar_add_meshStep hR i₀ z
    linarith
  have hsplit : ∫ z : Space d, ψ (z + h) * parityChar R (z + h) =
      (∫ z : Space d, ψ (z + h)) - ∫ z : Space d, ψ (z + h) * parityChar R z := by
    have hpt : ∀ z : Space d, ψ (z + h) * parityChar R (z + h) =
        ψ (z + h) - ψ (z + h) * parityChar R z := by
      intro z; rw [hflip z]; ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_sub hintT hintTχ]
  have hmeanT : ∫ z : Space d, ψ (z + h) = 0 := by
    rw [integral_add_right_eq_self ψ h, hmean]
  have hdouble : 2 * ∫ z : Space d, ψ z * parityChar R z =
      ∫ z : Space d, (ψ z - ψ (z + h)) * parityChar R z := by
    have h1 : ∫ z : Space d, ψ z * parityChar R z = -∫ z : Space d, ψ (z + h) * parityChar R z := by
      rw [hshift, hsplit, hmeanT]; ring
    have h2 : ∫ z : Space d, (ψ z - ψ (z + h)) * parityChar R z =
        (∫ z : Space d, ψ z * parityChar R z) - ∫ z : Space d, ψ (z + h) * parityChar R z := by
      have hpt : ∀ z : Space d, (ψ z - ψ (z + h)) * parityChar R z =
          ψ z * parityChar R z - ψ (z + h) * parityChar R z := by
        intro z; ring
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_sub hintψχ hintTχ]
    rw [h2, h1]; ring
  -- the bound
  have hd1 : Integrable (fun z : Space d => ψ z - ψ (z + h)) := by
    have := hint.sub hintT
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    rfl
  have hd1χ : Integrable (fun z : Space d => (ψ z - ψ (z + h)) * parityChar R z) :=
    hd1.mul_bdd hmχ.aestronglyMeasurable hbound
  have habs : |∫ z : Space d, (ψ z - ψ (z + h)) * parityChar R z| ≤
      ∫ z : Space d, |ψ z - ψ (z + h)| := by
    refine le_trans (abs_integral_le_integral_abs) ?_
    refine integral_mono hd1χ.abs hd1.abs fun z => ?_
    rw [abs_mul, abs_of_nonneg (parityChar_nonneg R z)]
    calc |ψ z - ψ (z + h)| * parityChar R z ≤ |ψ z - ψ (z + h)| * 1 :=
          mul_le_mul_of_nonneg_left (parityChar_le_one R z) (abs_nonneg _)
      _ = |ψ z - ψ (z + h)| := by ring
  have habs2 : |2 * ∫ z : Space d, ψ z * parityChar R z| ≤ ∫ z : Space d, |ψ z - ψ (z + h)| := by
    rw [hdouble]; exact habs
  rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)] at habs2
  linarith

end Sandpile.Support
