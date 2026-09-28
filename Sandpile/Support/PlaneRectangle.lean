import Sandpile.Support.CrossingDefinitions
import Sandpile.External.BallGreenBounds
import Sandpile.Support.FarComparison

/-!
# Fixed-aspect rectangles and an explicit far-field cutoff

Specializes the Gaussian comparison of `Sandpile.exists_gaussian_far_comparison` to the concrete
rectangles `planeRectangle w h = [0, w] × [0, h]`, embedded in a coordinate plane of `Site 4`
through a point `x` by `planeTranslate`, with aspect ratio `ϑ` fixed so that the cardinality bound
`Q.card ≤ r^m` of that comparison holds with the exponent `m = 3`. It also supplies an explicit
piecewise-linear cutoff `farCutoff`, proves it satisfies `External.BallGreen.IsCutoff`, and
assembles these pieces into `exists_gaussian_aspect_rectangle_comparison`, a comparison between
the crossing-value tail of the cut-off Green field and that of the corresponding Gaussian field.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal

noncomputable section

namespace Sandpile

/-- The lattice rectangle `[0, w] × [0, h]` in `Site 2`. -/
def planeRectangle (w h : ℕ) : Finset (Site 2) :=
  Fintype.piFinset (fun i => Finset.Icc (0 : ℤ) (![(w : ℤ), (h : ℤ)] i))

/-- `z` lies in `planeRectangle w h` iff both its coordinates lie in `[0, w]` and `[0, h]`
respectively. -/
lemma mem_planeRectangle (w h : ℕ) (z : Site 2) :
    z ∈ planeRectangle w h ↔ 0 ≤ z 0 ∧ z 0 ≤ w ∧ 0 ≤ z 1 ∧ z 1 ≤ h := by
  simp only [planeRectangle, Fintype.mem_piFinset, Finset.mem_Icc, Fin.forall_fin_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  tauto

/-- `planeRectangle w h` is a lattice rectangle in the sense of `IsLatticeRectangle`, with
corners `0` and `![w, h]`. -/
lemma isLatticeRectangle_planeRectangle (w h : ℕ) : IsLatticeRectangle (planeRectangle w h) := by
  refine ⟨0, ![w, h], ?_⟩
  intro z
  simp only [planeRectangle, Fintype.mem_piFinset, Finset.mem_Icc, Pi.zero_apply]

/-- `planeRectangle w h` has exactly `(w + 1) * (h + 1)` points. -/
lemma card_planeRectangle (w h : ℕ) : (planeRectangle w h).card = (w + 1) * (h + 1) := by
  simp [planeRectangle, Fintype.card_piFinset, Fin.prod_univ_two, Int.card_Icc]

/-- The height `h` is at most the number of points of `planeRectangle w h`. -/
lemma height_le_card_planeRectangle (w h : ℕ) : h ≤ (planeRectangle w h).card := by
  rw [card_planeRectangle]
  exact (Nat.le_succ h).trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos w))

/-- For aspect ratio `ϑ ≥ 1` and `r` large enough that `2(ϑ + 1) ≤ r`, the fixed-aspect
rectangle `planeRectangle ⌊ϑr⌋ r` has at most `r^3` points. -/
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
      _ ≤ ((ϑ + 1) * r) * (2 * r) :=
          mul_le_mul (by nlinarith) (by linarith) (by positivity) (by positivity)
      _ = (2 * (ϑ + 1)) * (r : ℝ) ^ 2 := by ring
      _ ≤ (r : ℝ) * (r : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hr (sq_nonneg _)
      _ = _ := by ring
  exact_mod_cast hcard

/-- Embeds `Site 2` into `Site 4` as the coordinate plane through `x`: the first two
coordinates of `z` are added to those of `x`, and the last two coordinates are fixed at those
of `x`. -/
def planeTranslate (x : Site 4) (z : Site 2) : Site 4 := ![x 0 + z 0, x 1 + z 1, x 2, x 3]

/-- The explicit piecewise-linear cutoff `max 0 (min 1 (x - 1))`, vanishing on `(-∞, 1]`,
equal to `1` on `[2, ∞)`, and linear in between. -/
def farCutoff (x : ℝ) : ℝ := max 0 (min 1 (x - 1))

/-- `farCutoff` is `1`-Lipschitz. -/
lemma lipschitzWith_farCutoff : LipschitzWith 1 farCutoff := by
  have hh : LipschitzWith 1 (fun x : ℝ => x - 1) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [dist_sub_right, NNReal.coe_one, one_mul, le_refl]
  exact (hh.const_min 1).const_max 0

/-- `farCutoff` satisfies `External.BallGreen.IsCutoff`: it takes values in `[0, 1]`, is
`2`-Lipschitz on `[0, ∞)`, vanishes on `[0, 1]`, and equals `1` on `[2, ∞)`. -/
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

/-- The Gaussian comparison of `exists_gaussian_far_comparison`, specialized to the fixed-aspect
rectangle `planeRectangle ⌊ϑr⌋ r` translated into the coordinate plane through `x` and to the
explicit cutoff `farCutoff`: the probability that the crossing value of the cut-off field is at
most `-a log r` is bounded by the corresponding Gaussian probability at the shifted level
`-(a - 3η) log r`, plus an error of order `(log r)^3 r^{-2α}`. -/
lemma exists_gaussian_aspect_rectangle_comparison (hBall : External.BallGreenBounds)
    (θ K α η ϑ : ℝ) (hθ : 0 < θ) (hα : 0 < α) (hη : 0 < η) (hϑ : 1 ≤ ϑ) :
    ∃ C > 0, ∃ r₀ : ℕ, ∀ (μ : Measure ℝ), IsProbabilityMeasure μ →
      Integrable (fun x : ℝ => Real.exp (θ * |x|)) μ →
      (∫ x : ℝ, Real.exp (θ * |x|) ∂μ) ≤ K → (∫ x : ℝ, x ∂μ) = 0 →
      ∀ v : ℝ≥0, (∫ x : ℝ, x ^ 2 ∂μ) = v → ∀ r : ℕ, r₀ ≤ r →
      ∀ x : Site 4, ∀ a : ℝ,
        (LatticeProb.iidLaw 4 μ).real
          {ζ | crossingValue (planeRectangle ⌊ϑ * r⌋₊ r) (fun w => finiteKernelField
            (External.BallGreen.cutField r ⌊(r : ℝ) ^ α⌋₊ farCutoff) ζ (planeTranslate x w))
              ≤ -a * Real.log r} ≤
        (LatticeProb.iidLaw 4 (gaussianReal 0 v)).real
          {ζ | crossingValue (planeRectangle ⌊ϑ * r⌋₊ r) (fun w => finiteKernelField
            (External.BallGreen.cutField r ⌊(r : ℝ) ^ α⌋₊ farCutoff) ζ (planeTranslate x w))
              ≤ -(a - 3 * η) * Real.log r} +
          C * (Real.log r) ^ 3 * (r : ℝ) ^ (-2 * α) := by
  obtain ⟨C, hC, r₀, hcomp⟩ := exists_gaussian_far_comparison hBall θ K α η hθ hα hη 3 (by decide)
  refine ⟨C, hC, max r₀ ⌈2 * (ϑ + 1)⌉₊, ?_⟩
  intro μ hμ hexp hK hmean v hsecond r hr x a
  have hr₀ : r₀ ≤ r := (le_max_left _ _).trans hr
  have hrϑ : 2 * (ϑ + 1) ≤ (r : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hr)
  have hh := hcomp μ hμ hexp hK hmean v hsecond r hr₀ (planeRectangle ⌊ϑ * r⌋₊ r)
    (isLatticeRectangle_planeRectangle _ _) (height_le_card_planeRectangle _ _)
    (card_planeRectangle_aspect_le_cube hϑ hrϑ) farCutoff isCutoff_farCutoff
    (fun w => planeTranslate x w) (-a * Real.log r)
  have he : -a * Real.log r + 3 * η * Real.log r = -(a - 3 * η) * Real.log r := by ring
  simpa only [he] using hh

end Sandpile
