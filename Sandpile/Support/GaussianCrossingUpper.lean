/-
Upper deviations of Gaussian finite-kernel crossing values from their means.
-/
import Sandpile.Support.GaussianBottleneck

open MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
namespace Sandpile

lemma subgaussian_centered_upper_tail {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ} {m : ℝ} {c : ℝ≥0}
    (hf : HasSubgaussianMGF (fun x => f x - m) c μ) {t : ℝ} (ht : 0 ≤ t) :
    μ {x | m + t ≤ f x} ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * c))) := by
  have he : {x | m + t ≤ f x} = {x | t ≤ f x - m} := by
    ext x
    simp only [Set.mem_setOf_eq]
    constructor <;> intro hh <;> linarith
  rw [he]
  have hh := hf.measure_ge_le ht
  change μ.real {x | t ≤ f x - m} ≤ _ at hh
  simpa only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)] using ENNReal.ofReal_le_ofReal hh

lemma exists_gaussian_far_crossing_upper_concentration (hBall : External.BallGreenBounds) :
    ∃ C > 0, ∀ r : ℕ, 2 ≤ r → ∀ L : ℕ, ∀ φ : ℝ → ℝ, External.BallGreen.IsCutoff φ →
      ∀ Q : Finset (Site 2), IsLatticeRectangle Q → 2 ≤ Q.card → ∀ z : Q → Site 4,
        ∀ v V : ℝ≥0, v ≤ V → ∀ t : ℝ, 0 ≤ t →
          LatticeProb.iidLaw 4 (gaussianReal 0 v)
            {ζ | (∫ ξ : Site 4 → ℝ,
                crossingValue Q (fun w => finiteKernelField (External.BallGreen.cutField r L φ) ξ (z w))
                ∂LatticeProb.iidLaw 4 (gaussianReal 0 v)) + t ≤
                crossingValue Q (fun w => finiteKernelField (External.BallGreen.cutField r L φ) ζ (z w))} ≤
            ENNReal.ofReal (Real.exp (-t ^ 2 / (C * V * Real.log r))) := by
  obtain ⟨G, hG, hsum⟩ := cutField_square_sum_bound hBall
  refine ⟨Real.pi ^ 2 * G / 2, by positivity, ?_⟩
  intro r hr L φ hφ Q hQ hN z v V hv t ht
  let D : ℝ≥0 := ⟨Real.sqrt ((V : ℝ) * G * Real.log r), Real.sqrt_nonneg _⟩
  have hn : 0 ≤ (V : ℝ) * G * Real.log r :=
    mul_nonneg (mul_nonneg V.coe_nonneg hG.le) (Real.log_natCast_nonneg r)
  have hD : (v : ℝ) * (∑' u : Site 4, External.BallGreen.cutField r L φ u ^ 2) ≤ (D : ℝ) ^ 2 := by
    change (v : ℝ) * (∑' u : Site 4, External.BallGreen.cutField r L φ u ^ 2) ≤
      Real.sqrt ((V : ℝ) * G * Real.log r) ^ 2
    rw [Real.sq_sqrt hn]
    calc
      _ ≤ (V : ℝ) * (∑' u : Site 4, External.BallGreen.cutField r L φ u ^ 2) :=
        mul_le_mul_of_nonneg_right (show (v : ℝ) ≤ V from hv) (tsum_nonneg (fun _ => sq_nonneg _))
      _ ≤ (V : ℝ) * (G * Real.log r) := mul_le_mul_of_nonneg_left (hsum r hr L φ hφ) V.coe_nonneg
      _ = _ := by ring
  have hSG := hasSubgaussianMGF_finiteKernel_crossing hQ hN (boxFinset 0 r)
    (fun u hu => cutField_eq_zero_of_notMem_boxFinset r L φ hu) (summable_cutField_sq r L φ) z v D hD
  have hp := subgaussian_centered_upper_tail hSG ht
  have hd : 2 * (Real.pi ^ 2 * (D : ℝ) ^ 2 / 4) = (Real.pi ^ 2 * G / 2) * V * Real.log r := by
    change 2 * (Real.pi ^ 2 * Real.sqrt ((V : ℝ) * G * Real.log r) ^ 2 / 4) = _
    rw [Real.sq_sqrt hn]
    ring
  change _ ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * (Real.pi ^ 2 * (D : ℝ) ^ 2 / 4)))) at hp
  rw [hd] at hp
  exact hp

end Sandpile
