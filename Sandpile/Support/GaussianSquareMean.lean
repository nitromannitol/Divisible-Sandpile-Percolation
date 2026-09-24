/-
A uniform mean lower bound and polynomial lower tails for Gaussian square crossings.
-/
import Sandpile.Support.RectangleDuality
import Sandpile.Support.GaussianSquareSymmetry

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
noncomputable section
namespace Sandpile

lemma integrable_vertical_gaussian_far_neg (r L w h : ℕ)
    (hN : 2 ≤ (planeRectangle h w).card) (φ : ℝ → ℝ) (x : Site 4) (v : ℝ≥0) :
    Integrable (fun ζ : Site 4 → ℝ => verticalCrossingValue w h (fun z =>
      -finiteKernelField (External.BallGreen.cutField r L φ) ζ (planeTranslate x z)))
        (LatticeProb.iidLaw 4 (gaussianReal 0 v)) := by
  have hi := integrable_gaussian_far_crossing (isLatticeRectangle_planeRectangle h w) hN r L φ
    (fun z : planeRectangle h w => planeTranslate x (transposeRectangle h w z)) v
  have hh := (measurePreserving_iid_gaussian_neg 4 v).integrable_comp_of_integrable hi
  simpa only [Function.comp_def, finiteKernelField_neg, verticalCrossingValue] using hh

lemma exists_gaussian_square_mean_lower_bound (hBall : External.BallGreenBounds) (V : ℝ≥0) :
    ∃ C > 0, ∀ r L s : ℕ, 2 ≤ r → 2 ≤ L → 1 ≤ s → (planeRectangle s s).card ≤ r ^ 3 →
      ∀ φ : ℝ → ℝ, External.BallGreen.IsCutoff φ → ∀ x : Site 4, ∀ v : ℝ≥0, v ≤ V →
        -C * Real.sqrt (Real.log r) ≤
          ∫ ζ : Site 4 → ℝ, crossingValue (planeRectangle s s) (fun z =>
            finiteKernelField (External.BallGreen.cutField r L φ) ζ (planeTranslate x z))
              ∂LatticeProb.iidLaw 4 (gaussianReal 0 v) := by
  obtain ⟨C, hC, hinc⟩ := exists_gaussian_rectangle_increment_bound hBall V
  refine ⟨C, hC, ?_⟩
  intro r L s hr hL hs hcard φ hφ x v hv
  letI : Nonempty (planeRectangle s s) := (planeRectangle_nonempty s s).to_subtype
  have hN : 2 ≤ (planeRectangle s s).card := by
    rw [card_planeRectangle]
    nlinarith
  let F (ζ : Site 4 → ℝ) (z : planeRectangle s s) :=
    finiteKernelField (External.BallGreen.cutField r L φ) ζ (planeTranslate x z)
  have hiH := integrable_gaussian_far_crossing (isLatticeRectangle_planeRectangle s s) hN r L φ
    (fun z : planeRectangle s s => planeTranslate x z) v
  have hiV := integrable_vertical_gaussian_far_neg r L s s hN φ x v
  obtain ⟨hiO, hO⟩ := hinc (planeRectangle s s) r L hr hL hcard φ hφ x v hv
  have hmean := integral_mono hiO.neg (hiH.add hiV) (fun ζ => crossingValue_add_vertical_neg_ge s s (F ζ))
  simp only [Pi.neg_apply, Pi.add_apply] at hmean
  rw [integral_neg, integral_add hiH hiV, integral_vertical_gaussian_far_eq_horizontal] at hmean
  have hnonneg : 0 ≤ C * Real.sqrt (Real.log r) := mul_nonneg hC.le (Real.sqrt_nonneg _)
  linarith

lemma exists_gaussian_square_lower_tail (hBall : External.BallGreenBounds)
    (V : ℝ≥0) (hV : 0 < V) :
    ∃ c > 0, ∀ a : ℝ, 0 < a → ∃ r₀ : ℕ, ∀ r L s : ℕ, r₀ ≤ r → 2 ≤ L → 1 ≤ s →
      (planeRectangle s s).card ≤ r ^ 3 → ∀ φ : ℝ → ℝ, External.BallGreen.IsCutoff φ →
      ∀ x : Site 4, ∀ v : ℝ≥0, v ≤ V →
        LatticeProb.iidLaw 4 (gaussianReal 0 v)
          {ζ | crossingValue (planeRectangle s s) (fun z =>
            finiteKernelField (External.BallGreen.cutField r L φ) ζ (planeTranslate x z)) ≤
              -(a * Real.log r)} ≤ ENNReal.ofReal ((r : ℝ) ^ (-(c * a ^ 2))) := by
  obtain ⟨B, _, hmean⟩ := exists_gaussian_square_mean_lower_bound hBall V
  obtain ⟨C, hC, hconc⟩ := exists_gaussian_far_crossing_concentration hBall
  have hVR : 0 < (V : ℝ) := hV
  refine ⟨1 / (4 * C * (V : ℝ)), by positivity, ?_⟩
  intro a ha
  have hsqrtlim : Tendsto (fun r : ℕ => Real.sqrt (Real.log (r : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hev : ∀ᶠ r : ℕ in atTop, 2 ≤ r ∧ 2 * B / a ≤ Real.sqrt (Real.log r) := by
    filter_upwards [eventually_ge_atTop 2, hsqrtlim.eventually (eventually_ge_atTop (2 * B / a))]
      with r hr hs
    exact ⟨hr, hs⟩
  obtain ⟨r₀, hr₀⟩ := hev.exists_forall_of_atTop
  refine ⟨r₀, ?_⟩
  intro r L s hr hL hs hcard φ hφ x v hv
  obtain ⟨hr2, hsqrt⟩ := hr₀ r hr
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hlog : 0 < Real.log (r : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < r))
  have hN : 2 ≤ (planeRectangle s s).card := by
    rw [card_planeRectangle]
    nlinarith
  have hsmall : B * Real.sqrt (Real.log r) ≤ a * Real.log r / 2 := by
    have hb := (div_le_iff₀ ha).mp hsqrt
    have hh := mul_le_mul_of_nonneg_right hb (Real.sqrt_nonneg (Real.log r))
    nlinarith [Real.sq_sqrt hlog.le]
  have hm := hmean r L s hr2 hL hs hcard φ hφ x v hv
  have hprob := hconc r hr2 L φ hφ (planeRectangle s s)
    (isLatticeRectangle_planeRectangle s s) hN (fun z => planeTranslate x z) v V hv
    (a * Real.log r / 2) (by positivity)
  have hexp : Real.exp (-(a * Real.log r / 2) ^ 2 / (C * (V : ℝ) * Real.log r)) =
      (r : ℝ) ^ (-(1 / (4 * C * (V : ℝ)) * a ^ 2)) := by
    rw [Real.rpow_def_of_pos hrpos]
    congr 1
    field_simp
    ring
  rw [hexp] at hprob
  apply le_trans (measure_mono ?_) hprob
  intro ζ hζ
  change crossingValue (planeRectangle s s) (fun z =>
    finiteKernelField (External.BallGreen.cutField r L φ) ζ (planeTranslate x z)) ≤ _ at hζ ⊢
  linarith

end Sandpile
