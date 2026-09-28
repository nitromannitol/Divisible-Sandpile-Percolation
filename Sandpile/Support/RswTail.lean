import Sandpile.Support.GaussianSquareMean
import Sandpile.Support.GaussianCrossingUpper
import Sandpile.Support.RswMeanLower
import Sandpile.Support.PlaneRectangle
import Sandpile.External.PlanarRSW

/-!
# RSW rectangle extension: polynomial lower tail

The RSW rectangle extension for Gaussian far-field crossing values: the final
polynomial lower tail for fixed-aspect rectangles, combining the RSW mean
lower bound with the sub-Gaussian lower concentration.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

noncomputable section
namespace Sandpile

/-- For every positive variance bound `V` there is `c > 0` such that for every
`a > 0` there is `r₀` with: for every `r ≥ r₀`, every cutoff field, every
translate and every `v ≤ V`, the Gaussian far-field crossing value of the
fixed-aspect rectangle `planeRectangle ⌊ϑ r⌋₊ r` is below `-a log r` with
probability at most `r^(-c a²)`. -/
theorem gaussian_far_rectangle_lower_tail
    (hRSW : Sandpile.External.PlanarRSW)
    (hBall : External.BallGreenBounds) (V : ℝ≥0) (hV : 0 < V) (ϑ : ℝ) (hϑ : 1 ≤ ϑ) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : ℝ, 0 < a → ∃ r₀ : ℕ, ∀ r L : ℕ, r₀ ≤ r → 2 ≤ L →
      ∀ φ : ℝ → ℝ, External.BallGreen.IsCutoff φ → ∀ x : Site 4, ∀ v : ℝ≥0, v ≤ V →
        LatticeProb.iidLaw 4 (ProbabilityTheory.gaussianReal 0 v)
          {ζ | crossingValue (planeRectangle ⌊ϑ * r⌋₊ r) (fun w =>
            finiteKernelField (External.BallGreen.cutField r L φ) ζ (planeTranslate x w)) ≤
              -(a * Real.log r)} ≤
        ENNReal.ofReal ((r : ℝ) ^ (-(c * a ^ 2)))
:= by
  obtain ⟨C, hC, hconc⟩ := exists_gaussian_far_crossing_concentration hBall
  obtain ⟨-, -, hmean⟩ := exists_gaussian_rectangle_mean_lower hRSW hBall V hV ϑ hϑ
  refine ⟨1 / (4 * C * V), by positivity, fun a ha => ?_⟩
  obtain ⟨r₁, hr₁⟩ := hmean a ha
  refine ⟨max r₁ 2, fun r L hr hL φ hφ x v hv => ?_⟩
  have hr2 : 2 ≤ r := le_trans (by omega) hr
  -- the mean lower bound at this r
  have hmean' := hr₁ r L (le_trans (le_max_left _ _) hr) hL φ hφ x v hv
  -- event inclusion into the centered lower tail at t = (a/2) log r
  have hsub : {ζ : Site 4 → ℝ | crossingValue (planeRectangle ⌊ϑ * r⌋₊ r) (fun w =>
      finiteKernelField (External.BallGreen.cutField r L φ) ζ (planeTranslate x w)) ≤
      -(a * Real.log r)}
      ⊆ {ζ : Site 4 → ℝ | crossingValue (planeRectangle ⌊ϑ * r⌋₊ r) (fun w =>
      finiteKernelField (External.BallGreen.cutField r L φ) ζ (planeTranslate x w)) ≤
      (∫ ξ : Site 4 → ℝ, crossingValue (planeRectangle ⌊ϑ * r⌋₊ r) (fun w =>
        finiteKernelField (External.BallGreen.cutField r L φ) ξ (planeTranslate x w))
        ∂LatticeProb.iidLaw 4 (gaussianReal 0 v)) - (a / 2) * Real.log r} := by
    intro ζ hζ
    simp only [Set.mem_setOf_eq] at hζ ⊢
    linarith
  have hmono := measure_mono (μ := LatticeProb.iidLaw 4 (gaussianReal 0 v)) hsub
  have hcard : 2 ≤ (planeRectangle ⌊ϑ * r⌋₊ r).card := by
    rw [card_planeRectangle]
    have h1 : 1 ≤ r := by omega
    have h2 : 1 * 2 ≤ (⌊ϑ * r⌋₊ + 1) * (r + 1) :=
      Nat.mul_le_mul (Nat.succ_le_succ (Nat.zero_le _)) (Nat.succ_le_succ h1)
    omega
  have hconc' := hconc r hr2 L φ hφ (planeRectangle ⌊ϑ * r⌋₊ r)
    (isLatticeRectangle_planeRectangle _ _) hcard
    (fun w => planeTranslate x (w : Site 2)) v V hv ((a / 2) * Real.log r)
    (by positivity)
  -- the exponential equals r^(-c a^2)
  have hexp : Real.exp (-((a / 2) * Real.log r) ^ 2 / (C * V * Real.log r))
      = (r : ℝ) ^ (-(1 / (4 * C * V) * a ^ 2)) := by
    have h3 : (0:ℝ) < Real.log r := Real.log_pos (by exact_mod_cast hr2)
    have h4 : (0:ℝ) < C * V * Real.log r := by positivity
    have h5 : (r : ℝ) ^ (-(1 / (4 * C * V) * a ^ 2))
        = Real.exp (-(1 / (4 * C * V) * a ^ 2) * Real.log r) := by
      have hrpos : (0:ℝ) < (r:ℝ) := by exact_mod_cast (by omega : 1 ≤ r)
      calc (r : ℝ) ^ (-(1 / (4 * C * V) * a ^ 2))
          = Real.exp (Real.log ((r : ℝ) ^ (-(1 / (4 * C * V) * a ^ 2)))) :=
            (Real.exp_log (Real.rpow_pos_of_pos hrpos _)).symm
        _ = Real.exp (-(1 / (4 * C * V) * a ^ 2) * Real.log r) := by
            rw [Real.log_rpow hrpos]
    rw [h5]
    congr 1
    field_simp
    ring
  rw [hexp] at hconc'
  exact le_trans hmono hconc'

end Sandpile