import Sandpile.Support.ContCell

/-!
# The `L²` bound on the tested cell masses

Each `φ_R(x)` is the integral of a test function `φ` over a cell of volume `R^{-d}`, so
the Cauchy-Schwarz inequality gives `φ_R(x)² ≤ R^{-d} ∫ φ²` over that cell; summing over
finitely many cells, which are disjoint, gives `∑_x a_R(x)² ≤ C(φ) R^{-4}` for the scaled
masses `a_R(x) = R^{(d-4)/2} φ_R(x)`. The Cauchy-Schwarz step `(∫_A f)² ≤ μ(A) ∫_A f²` is
proved from the discriminant of the nonnegative quadratic `t ↦ ∫_A (f - t)²`, and the sum
of the cell integrals of `φ²` is bounded by the integral of `φ²` over all of `ℝ^d`.
-/

open MeasureTheory Filter Topology
open Sandpile.Continuum

namespace Sandpile

/-- The Cauchy-Schwarz bound `(∫_A f)² ≤ μ.real(A) * ∫_A f²`, proved from the
nonnegativity of `∫_A (f - t)²` for every real `t`, taking `t = m / V` when the measure
`V` of `A` is positive and handling the null case separately. -/
theorem sq_setIntegral_le {α : Type*} [MeasurableSpace α] (μ : Measure α) (A : Set α)
    (f : α → ℝ) (hf : IntegrableOn f A μ) (hf2 : IntegrableOn (fun z => f z ^ 2) A μ)
    (hA : μ A ≠ ⊤) :
    (∫ z in A, f z ∂μ) ^ 2 ≤ (μ.real A) * ∫ z in A, f z ^ 2 ∂μ := by
  set ν : Measure α := μ.restrict A with hν
  set m : ℝ := ∫ z, f z ∂ν with hm
  set S : ℝ := ∫ z, f z ^ 2 ∂ν with hS
  set V : ℝ := μ.real A with hV
  haveI : IsFiniteMeasure ν := ⟨by
    rw [hν, Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hA⟩
  have hVint : ∫ _z, (1 : ℝ) ∂ν = V := by
    rw [integral_const, smul_eq_mul, mul_one, hν, hV, measureReal_def,
      Measure.restrict_apply_univ]
    rfl
  have hexp : ∀ t : ℝ, ∫ z, (f z - t) ^ 2 ∂ν = S - 2 * t * m + t ^ 2 * V := by
    intro t
    have hpt : ∀ z, (f z - t) ^ 2 = f z ^ 2 - 2 * t * f z + t ^ 2 * 1 := fun z => by ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    have hi1 : Integrable (fun z => f z ^ 2 - 2 * t * f z) ν := hf2.sub (hf.const_mul _)
    have hi2 : Integrable (fun _z : α => t ^ 2 * (1 : ℝ)) ν := (integrable_const _).const_mul _
    rw [integral_add hi1 hi2, integral_sub hf2 (hf.const_mul _), integral_const_mul,
      integral_const_mul, hVint]
  have hnn : ∀ t : ℝ, 0 ≤ S - 2 * t * m + t ^ 2 * V := by
    intro t
    rw [← hexp t]
    exact integral_nonneg fun z => sq_nonneg _
  have hV0 : 0 ≤ V := measureReal_nonneg
  rcases eq_or_lt_of_le hV0 with hVz | hVpos
  · -- the cell is null, so both sides vanish
    have hSnn : 0 ≤ S := integral_nonneg fun z => sq_nonneg _
    have hm0 : m = 0 := by
      by_contra hmne
      have h1 := hnn ((S + 1) / m)
      rw [← hVz] at h1
      have hmul : (S + 1) / m * m = S + 1 := div_mul_cancel₀ _ hmne
      nlinarith [h1, hmul, hSnn]
    rw [hm0]
    nlinarith [hSnn, hV0, hVz]
  · have h := hnn (m / V)
    have hne : V ≠ 0 := ne_of_gt hVpos
    have h1 : (m / V) ^ 2 * V = m ^ 2 / V := by field_simp
    have h2 : 2 * (m / V) * m = 2 * (m ^ 2 / V) := by field_simp
    rw [h1, h2] at h
    have h3 : m ^ 2 / V ≤ S := by linarith
    rw [div_le_iff₀ hVpos] at h3
    nlinarith [h3]

variable {d : ℕ}

/-- The square of a test function `φ` is integrable, since `φ` is continuous with
compact support and squaring preserves compact support of the vanishing locus. -/
theorem integrable_sq_of_isTestFn {φ : Space d → ℝ}
    (hφ : Sandpile.Continuum.IsTestFn Set.univ φ) :
    Integrable (fun z => φ z ^ 2) (volume : Measure (Space d)) := by
  obtain ⟨hsmooth, hcomp, -⟩ := hφ
  have hcont : Continuous φ := hsmooth.continuous
  refine (hcont.pow 2).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro hcomp.isCompact ?_
  intro z hz
  have hz0 : φ z = 0 := image_eq_zero_of_notMem_tsupport hz
  simp [hz0]

/-- The real-valued volume of a cell `Sandpile.Support.cell d R x` of side length
`R⁻¹` is `R⁻¹ ^ d`. -/
theorem measureReal_cell {R : ℝ} (hR : 0 < R) (x : Sandpile.Site d) :
    (volume : Measure (Space d)).real (Sandpile.Support.cell d R x) = R⁻¹ ^ d := by
  rw [MeasureTheory.measureReal_def, Sandpile.Support.volume_cell d hR x, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (le_of_lt (inv_pos.mpr hR))]

/-- The square of one tested cell mass `Sandpile.Support.cellMass R φ x` is at most
`R⁻¹ ^ d` times the integral of `φ²` over that cell, by the Cauchy-Schwarz bound
`sq_setIntegral_le` applied to the cell's finite volume. -/
theorem sq_cellMass_le {R : ℝ} (hR : 0 < R) {φ : Space d → ℝ}
    (hφ : Sandpile.Continuum.IsTestFn Set.univ φ) (x : Sandpile.Site d) :
    (Sandpile.Support.cellMass R φ x) ^ 2
      ≤ R⁻¹ ^ d * ∫ z in Sandpile.Support.cell d R x, φ z ^ 2 := by
  obtain ⟨C, L, hC, hL, hCb, hLb, hint⟩ := Sandpile.Support.exists_bound_of_isTestFn hφ
  have hint2 : Integrable (fun z => φ z ^ 2) (volume : Measure (Space d)) :=
    integrable_sq_of_isTestFn hφ
  have hfin : (volume : Measure (Space d)) (Sandpile.Support.cell d R x) ≠ ⊤ := by
    rw [Sandpile.Support.volume_cell d hR x]
    exact (ENNReal.pow_lt_top ENNReal.ofReal_lt_top).ne
  have h := sq_setIntegral_le (volume : Measure (Space d)) (Sandpile.Support.cell d R x) φ
    hint.integrableOn hint2.integrableOn hfin
  rwa [measureReal_cell hR x] at h

/-- The sum, over a finite set of sites `s`, of the squared tested cell masses is at
most `R⁻¹ ^ d` times the integral of `φ²` over all of `Space d`, since the cells are
disjoint and their union has integral at most that of the whole space. -/
theorem sum_sq_cellMass_le {R : ℝ} (hR : 0 < R) {φ : Space d → ℝ}
    (hφ : Sandpile.Continuum.IsTestFn Set.univ φ) (s : Finset (Sandpile.Site d)) :
    ∑ x ∈ s, (Sandpile.Support.cellMass R φ x) ^ 2
      ≤ R⁻¹ ^ d * ∫ z, φ z ^ 2 ∂(volume : Measure (Space d)) := by
  have hint2 : Integrable (fun z => φ z ^ 2) (volume : Measure (Space d)) :=
    integrable_sq_of_isTestFn hφ
  have hstep : ∑ x ∈ s, (Sandpile.Support.cellMass R φ x) ^ 2
      ≤ ∑ x ∈ s, R⁻¹ ^ d * ∫ z in Sandpile.Support.cell d R x, φ z ^ 2 :=
    Finset.sum_le_sum fun x _ => sq_cellMass_le hR hφ x
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

/-- **`eq:dgt4-tested-cell-l2`** (`sandpile.tex:5694-5697`) in the normalization
of the lemma: with `a_R(x) = R^{(d-4)/2} φ_R(x)`, the tested cell masses satisfy
`∑_x a_R(x)^2 ≤ C(φ) R^{-4}`, uniformly in the finite set of cells. -/
theorem sum_sq_scaled_cellMass_le {R : ℝ} (hR : 0 < R) {φ : Space d → ℝ}
    (hφ : Sandpile.Continuum.IsTestFn Set.univ φ) (s : Finset (Sandpile.Site d)) :
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
        mul_le_mul_of_nonneg_left (sum_sq_cellMass_le hR hφ s) (by positivity)
    _ = (∫ z, φ z ^ 2 ∂(volume : Measure (Space d))) * R ^ (-(4 : ℝ)) := by
        rw [hpow, hinv, ← mul_assoc, hmul]
        ring

end Sandpile
