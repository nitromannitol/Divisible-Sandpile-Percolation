/-
Fixed-aspect lattice rectangles, an explicit far-field cutoff, and
the logarithmic Gaussian comparison in translated coordinate planes.
-/
import Sandpile.Support.CrossingDefinitions
import Sandpile.External.BallGreenBounds
import Sandpile.Support.FarComparison

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal

noncomputable section

namespace Sandpile

def planeRectangle (w h : ℕ) : Finset (Site 2) :=
  Fintype.piFinset (fun i => Finset.Icc (0 : ℤ) (![(w : ℤ), (h : ℤ)] i))

lemma mem_planeRectangle (w h : ℕ) (z : Site 2) :
    z ∈ planeRectangle w h ↔ 0 ≤ z 0 ∧ z 0 ≤ w ∧ 0 ≤ z 1 ∧ z 1 ≤ h := by
  simp only [planeRectangle, Fintype.mem_piFinset, Finset.mem_Icc, Fin.forall_fin_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  tauto

lemma isLatticeRectangle_planeRectangle (w h : ℕ) : IsLatticeRectangle (planeRectangle w h) := by
  refine ⟨0, ![w, h], ?_⟩
  intro z
  simp only [planeRectangle, Fintype.mem_piFinset, Finset.mem_Icc, Pi.zero_apply]

lemma card_planeRectangle (w h : ℕ) : (planeRectangle w h).card = (w + 1) * (h + 1) := by
  simp [planeRectangle, Fintype.card_piFinset, Fin.prod_univ_two, Int.card_Icc]

lemma height_le_card_planeRectangle (w h : ℕ) : h ≤ (planeRectangle w h).card := by
  rw [card_planeRectangle]
  exact (Nat.le_succ h).trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos w))

lemma card_planeRectangle_aspect_le_cube {ϑ : ℝ} (hϑ : 1 ≤ ϑ) {r : ℕ}
    (hr : 2 * (ϑ + 1) ≤ (r : ℝ)) : (planeRectangle ⌊ϑ * r⌋₊ r).card ≤ r ^ 3 := by
  have hr1 : (1 : ℝ) ≤ r := by linarith
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hϑ0 : 0 ≤ ϑ := by linarith
  have hfloor := Nat.floor_le (mul_nonneg hϑ0 hr0)
  have hcard : ((planeRectangle ⌊ϑ * r⌋₊ r).card : ℝ) ≤ (r : ℝ) ^ 3 := by
    rw [card_planeRectangle]
    push_cast
    calc
      _ ≤ (ϑ * r + 1) * ((r : ℝ) + 1) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ ≤ ((ϑ + 1) * r) * (2 * r) := mul_le_mul (by nlinarith) (by linarith) (by positivity) (by positivity)
      _ = (2 * (ϑ + 1)) * (r : ℝ) ^ 2 := by ring
      _ ≤ (r : ℝ) * (r : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hr (sq_nonneg _)
      _ = _ := by ring
  exact_mod_cast hcard

def planeTranslate (x : Site 4) (z : Site 2) : Site 4 := ![x 0 + z 0, x 1 + z 1, x 2, x 3]

def farCutoff (x : ℝ) : ℝ := max 0 (min 1 (x - 1))

lemma lipschitzWith_farCutoff : LipschitzWith 1 farCutoff := by
  have hh : LipschitzWith 1 (fun x : ℝ => x - 1) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [dist_sub_right, NNReal.coe_one, one_mul, le_refl]
  exact (hh.const_min 1).const_max 0

lemma isCutoff_farCutoff : External.BallGreen.IsCutoff farCutoff := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x _
    exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  · intro x y _ _
    have hh := lipschitzWith_farCutoff.dist_le_mul x y
    simp only [Real.dist_eq, NNReal.coe_one, one_mul] at hh
    linarith [abs_nonneg (x - y)]
  · intro x _ hx
    unfold farCutoff
    have hm : min 1 (x - 1) ≤ 0 := (min_le_right _ _).trans (by linarith)
    exact max_eq_left hm
  · intro x hx
    unfold farCutoff
    rw [min_eq_left (by linarith)]
    norm_num

lemma exists_gaussian_aspect_rectangle_comparison (hBall : External.BallGreenBounds)
    (θ K α η ϑ : ℝ) (hθ : 0 < θ) (hα : 0 < α) (hη : 0 < η) (hϑ : 1 ≤ ϑ) :
    ∃ C > 0, ∃ r₀ : ℕ, ∀ (μ : Measure ℝ), IsProbabilityMeasure μ →
      Integrable (fun x : ℝ => Real.exp (θ * |x|)) μ →
      (∫ x : ℝ, Real.exp (θ * |x|) ∂μ) ≤ K → (∫ x : ℝ, x ∂μ) = 0 →
      ∀ v : ℝ≥0, (∫ x : ℝ, x ^ 2 ∂μ) = v → ∀ r : ℕ, r₀ ≤ r →
      ∀ x : Site 4, ∀ a : ℝ,
        (LatticeProb.iidLaw 4 μ).real
          {ζ | crossingValue (planeRectangle ⌊ϑ * r⌋₊ r) (fun w => finiteKernelField
            (External.BallGreen.cutField r ⌊(r : ℝ) ^ α⌋₊ farCutoff) ζ (planeTranslate x w)) ≤ -a * Real.log r} ≤
        (LatticeProb.iidLaw 4 (gaussianReal 0 v)).real
          {ζ | crossingValue (planeRectangle ⌊ϑ * r⌋₊ r) (fun w => finiteKernelField
            (External.BallGreen.cutField r ⌊(r : ℝ) ^ α⌋₊ farCutoff) ζ (planeTranslate x w)) ≤ -(a - 3 * η) * Real.log r} +
          C * (Real.log r) ^ 3 * (r : ℝ) ^ (-2 * α) := by
  obtain ⟨C, hC, r₀, hcomp⟩ := exists_gaussian_far_comparison hBall θ K α η hθ hα hη 3 (by decide)
  refine ⟨C, hC, max r₀ ⌈2 * (ϑ + 1)⌉₊, ?_⟩
  intro μ hμ hexp hK hmean v hsecond r hr x a
  have hr₀ : r₀ ≤ r := (le_max_left _ _).trans hr
  have hrϑ : 2 * (ϑ + 1) ≤ (r : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hr)
  have hh := hcomp μ hμ hexp hK hmean v hsecond r hr₀ (planeRectangle ⌊ϑ * r⌋₊ r)
    (isLatticeRectangle_planeRectangle _ _) (height_le_card_planeRectangle _ _)
    (card_planeRectangle_aspect_le_cube hϑ hrϑ) farCutoff isCutoff_farCutoff
    (fun w => planeTranslate x w) (-a * Real.log r)
  have he : -a * Real.log r + 3 * η * Real.log r = -(a - 3 * η) * Real.log r := by ring
  simpa only [he] using hh

end Sandpile
