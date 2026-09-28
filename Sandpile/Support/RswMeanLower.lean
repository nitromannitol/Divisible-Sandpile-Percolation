import Sandpile.Support.RswSquareHalf
import Sandpile.Support.RswHardStep
import Sandpile.Support.RswRectangleLower
import Sandpile.Support.RpowNegSmall
import Sandpile.Support.GaussianCrossingUpper
import Sandpile.Support.GaussianBottleneck
import Sandpile.External.PlanarRSW

/-!
# The RSW mean lower bound for Gaussian rectangle crossings

The RSW mean lower bound for Gaussian far-field rectangle crossings, and the final polynomial
lower tail for fixed-aspect rectangles.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
noncomputable section
namespace Sandpile

/-- The mean of the far-field crossing value of the fixed-aspect rectangle is
eventually at least `-(a/2) log r`: otherwise the fixed positive RSW crossing
probability would be trapped inside an exponentially small centered upper
tail. -/
lemma exists_gaussian_rectangle_mean_lower (hRSW : External.PlanarRSW)
    (hBall : External.BallGreenBounds) (V : ℝ≥0) (hV : 0 < V) (ϑ : ℝ) (hϑ : 1 ≤ ϑ) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ, 0 < a → ∃ r₀ : ℕ, ∀ r L : ℕ, r₀ ≤ r → 2 ≤ L →
      ∀ φ : ℝ → ℝ, External.BallGreen.IsCutoff φ → ∀ x : Site 4, ∀ v : ℝ≥0, v ≤ V →
        -(a / 2) * Real.log r ≤
          ∫ ζ : Site 4 → ℝ, crossingValue (planeRectangle ⌊ϑ * r⌋₊ r) (fun z =>
            finiteKernelField (External.BallGreen.cutField r L φ) ζ (planeTranslate x z))
            ∂LatticeProb.iidLaw 4 (gaussianReal 0 v) := by
  obtain ⟨q, hq, hlow⟩ := exists_gaussian_rectangle_crossing_lower hRSW hBall V hV ϑ hϑ
  obtain ⟨C, hC, hconc⟩ := exists_gaussian_far_crossing_upper_concentration hBall
  refine ⟨1, by norm_num, fun a ha => ?_⟩
  obtain ⟨r₁, hr₁⟩ := hlow a ha
  obtain ⟨r₂, hr₂⟩ := exists_rpow_neg_small (a ^ 2 / (16 * C * V)) q
    (by positivity) hq
  refine ⟨max (max r₁ r₂) 2, fun r L hr hL φ hφ x v hv => ?_⟩
  by_cases hmean : -(a / 2) * Real.log r ≤
      ∫ ζ : Site 4 → ℝ, crossingValue (planeRectangle ⌊ϑ * r⌋₊ r) (fun z =>
        finiteKernelField (External.BallGreen.cutField r L φ) ζ (planeTranslate x z))
        ∂LatticeProb.iidLaw 4 (gaussianReal 0 v)
  · exact hmean
  · exfalso
    set E : ℝ := ∫ ζ : Site 4 → ℝ, crossingValue (planeRectangle ⌊ϑ * r⌋₊ r) (fun z =>
        finiteKernelField (External.BallGreen.cutField r L φ) ζ (planeTranslate x z))
        ∂LatticeProb.iidLaw 4 (gaussianReal 0 v) with hE
    have hElt : E < -(a / 2) * Real.log r := lt_of_not_ge hmean
    -- the RSW event sits inside the centered upper tail at t = (a/4) log r
    have hsub : {ζ : Site 4 → ℝ | -(a / 4 * Real.log r) ≤ crossingValue
        (planeRectangle ⌊ϑ * r⌋₊ r) (fun z =>
          finiteKernelField (External.BallGreen.cutField r L φ) ζ (planeTranslate x z))}
        ⊆ {ζ : Site 4 → ℝ | E + (a / 4) * Real.log r ≤ crossingValue
        (planeRectangle ⌊ϑ * r⌋₊ r) (fun z =>
          finiteKernelField (External.BallGreen.cutField r L φ) ζ (planeTranslate x z))} := by
      intro ζ hζ
      have h1 : E + (a / 4) * Real.log r < -(a / 4) * Real.log r := by linarith
      have hζ' := hζ
      simp only [Set.mem_setOf_eq] at hζ'
      simp only [Set.mem_setOf_eq]
      linarith
    have hmono := measure_mono (μ := LatticeProb.iidLaw 4 (gaussianReal 0 v)) hsub
    have hcard : 2 ≤ (planeRectangle ⌊ϑ * r⌋₊ r).card := by
      rw [card_planeRectangle]
      have h1 : 1 ≤ r := by omega
      have h2 : 1 * 2 ≤ (⌊ϑ * r⌋₊ + 1) * (r + 1) :=
        Nat.mul_le_mul (Nat.succ_le_succ (Nat.zero_le _)) (Nat.succ_le_succ h1)
      omega
    have hconc' := hconc r (le_trans (by omega) hr) L φ hφ (planeRectangle ⌊ϑ * r⌋₊ r)
      (isLatticeRectangle_planeRectangle _ _) hcard
      (fun w => planeTranslate x (w : Site 2)) v V hv ((a / 4) * Real.log r)
      (by positivity)
    rw [← hE] at hconc'
    have hlow' :=
      hr₁ r L (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hr) hL φ hφ x v hv
    have hchain : ENNReal.ofReal q ≤ ENNReal.ofReal
      (Real.exp (-((a / 4) * Real.log r) ^ 2 / (C * V * Real.log r))) := by
      refine le_trans hlow' ?_
      refine le_trans hmono ?_
      exact hconc'
    -- the exponential is eventually below q
    have hexp : Real.exp (-((a / 4) * Real.log r) ^ 2 / (C * V * Real.log r))
        = Real.exp (-(a ^ 2 / (16 * C * V)) * Real.log r) := by
      have hr2 : 2 ≤ r := le_trans (by omega) hr
      have h3 : (0:ℝ) < Real.log r := Real.log_pos (by exact_mod_cast hr2)
      have h4 : (0:ℝ) < C * V * Real.log r := by positivity
      congr 1
      field_simp
      ring
    rw [hexp] at hchain
    have hsmall := hr₂ r
      (le_trans (le_trans (le_max_right r₁ r₂) (le_max_left (max r₁ r₂) 2)) hr)
    have hstrict : ENNReal.ofReal
        (Real.exp (-(a ^ 2 / (16 * C * V)) * Real.log r)) < ENNReal.ofReal q :=
      (ENNReal.ofReal_lt_ofReal_iff hq).mpr hsmall
    exact lt_irrefl _ (lt_of_le_of_lt hchain hstrict)


end Sandpile