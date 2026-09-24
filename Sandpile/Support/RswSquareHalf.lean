/-
The square crossing probability at a small negative level is eventually at
least one half, from the polynomial Gaussian lower tail for squares.
-/
import Sandpile.Support.GaussianSquareMean
import Sandpile.Support.RectangleMonotonicity
import Sandpile.Support.RswArithmetic
import Sandpile.Support.CrossingContinuity

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
noncomputable section
namespace Sandpile

lemma exists_gaussian_square_crossing_ge_half (hBall : External.BallGreenBounds)
    (V : ℝ≥0) (hV : 0 < V) :
    ∀ b : ℝ, 0 < b → ∃ r₀ : ℕ, ∀ r L : ℕ, r₀ ≤ r → 2 ≤ L →
      ∀ φ : ℝ → ℝ, External.BallGreen.IsCutoff φ → ∀ x : Site 4, ∀ v : ℝ≥0, v ≤ V →
        (1 : ℝ≥0∞) / 2 ≤ LatticeProb.iidLaw 4 (gaussianReal 0 v)
          {ζ | -(b * Real.log r) ≤ crossingValue (planeRectangle (2 * r) (2 * r))
            (fun z => finiteKernelField (External.BallGreen.cutField r L φ) ζ
              (planeTranslate x z))} := by
  obtain ⟨c, hc, htail⟩ := exists_gaussian_square_lower_tail hBall V hV
  intro b hb
  obtain ⟨r₁, h₁⟩ := htail b hb
  have hev : ∀ᶠ r : ℕ in atTop, (r : ℝ) ^ (-(c * b ^ 2)) ≤ (1 : ℝ) / 2 :=
    eventually_rpow_neg_le (by positivity) (by norm_num)
  rw [Filter.eventually_atTop (p := fun r : ℕ => (r : ℝ) ^ (-(c * b ^ 2)) ≤ (1 : ℝ) / 2)] at hev
  obtain ⟨r₂, hr₂⟩ := hev
  refine ⟨7 ⊔ r₁ ⊔ r₂, ?_⟩
  intro r L hr hL φ hφ x v hv
  have h7 : 7 ≤ r := le_trans (by omega) hr
  have hA := h₁ r L (2 * r) (by omega) hL (by omega) (card_double_square_le_cube h7) φ hφ x v hv
  set μ := LatticeProb.iidLaw 4 (gaussianReal 0 v) with hμ
  set Lsq : (Site 4 → ℝ) → ℝ := fun ζ => crossingValue (planeRectangle (2 * r) (2 * r))
    (fun z => finiteKernelField (External.BallGreen.cutField r L φ) ζ (planeTranslate x z)) with hLsq
  have hf : Measurable Lsq := by
    have hQ : IsLatticeRectangle (planeRectangle (2 * r) (2 * r)) :=
      isLatticeRectangle_planeRectangle _ _
    have hN : (planeRectangle (2 * r) (2 * r)).Nonempty := ⟨0, by
      simp only [mem_planeRectangle]; norm_num⟩
    exact (measurable_crossingValue hQ hN).comp (measurable_pi_lambda _ (fun z =>
      measurable_finiteKernelField (boxFinset 0 r)
        (fun _ hu => cutField_eq_zero_of_notMem_boxFinset r L φ hu) (planeTranslate x z)))
  have hmeas : MeasurableSet {ζ | Lsq ζ < -(b * Real.log r)} :=
    measurableSet_lt hf measurable_const
  have hAc : {ζ | -(b * Real.log r) ≤ Lsq ζ} = {ζ | Lsq ζ < -(b * Real.log r)}ᶜ := by
    ext ζ; simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
    constructor
    · intro h h'
      exact absurd h' (by
        have h1 : Lsq ζ < -(b * Real.log r) := h'
        have h2 : -(b * Real.log r) ≤ Lsq ζ := h
        linarith)
    · intro h
      exact not_lt.mp h
  have hsub : {ζ | Lsq ζ < -(b * Real.log r)} ⊆ {ζ | Lsq ζ ≤ -(b * Real.log r)} := by
    intro ζ hζ
    simp only [Set.mem_setOf_eq] at hζ ⊢
    exact hζ.le
  have hreal : μ.real {ζ | Lsq ζ ≤ -(b * Real.log r)} ≤ (r : ℝ) ^ (-(c * b ^ 2)) := by
    have hA' := hA
    rw [hμ] at hA'
    have h5 : (μ {ζ | Lsq ζ ≤ -(b * Real.log r)}).toReal ≤ (r : ℝ) ^ (-(c * b ^ 2)) :=
      ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity) |>.mp hA'
    have h6 : μ.real {ζ | Lsq ζ ≤ -(b * Real.log r)} = (μ {ζ | Lsq ζ ≤ -(b * Real.log r)}).toReal :=
      rfl
    rw [h6]
    exact h5
  have hcompl : μ.real {ζ | -(b * Real.log r) ≤ Lsq ζ} ≥ (1 : ℝ) / 2 := by
    have h3 : μ.real {ζ | Lsq ζ < -(b * Real.log r)} +
        μ.real {ζ | Lsq ζ < -(b * Real.log r)}ᶜ = μ.real Set.univ :=
      measureReal_add_measureReal_compl hmeas
    have h4 : μ.real {ζ | Lsq ζ < -(b * Real.log r)} ≤ (1 : ℝ) / 2 :=
      le_trans (le_trans (measureReal_mono hsub (measure_ne_top _ _)) hreal) (hr₂ r (by omega))
    rw [probReal_univ] at h3
    rw [hAc]
    linarith
  have hfin : μ {ζ | -(b * Real.log r) ≤ Lsq ζ} ≠ ⊤ :=
    measure_ne_top _ _
  rw [← ENNReal.ofReal_toReal hfin]
  rw [ENNReal.le_ofReal_iff_toReal_le (by norm_num) (by positivity)]
  have h7' : ((1 : ℝ≥0∞) / 2).toReal = (1 : ℝ) / 2 := by norm_num
  rw [h7']
  exact hcompl

end Sandpile