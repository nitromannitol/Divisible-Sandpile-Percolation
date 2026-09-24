/-
Uniform Gaussian comparison for rectangle crossing bottlenecks, including
finite-coefficient fields and the cut-off ball Green field.
-/
import Sandpile.Support.BottleneckComparison
import Sandpile.Support.StableBottleneck
import Sandpile.Support.CrossingContinuity
import Sandpile.Support.FiniteKernel

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal

namespace Sandpile

lemma rectangle_comparison_scale_le {B l₀ l e : ℝ} {n : ℕ}
    (hB : 0 ≤ B) (h₀ : 0 < l₀) (hl : l₀ ≤ l) (he : 0 < e)
    (hn : (n : ℝ) ≤ B * l) :
    (B * l ^ 2 / e) ^ 2 * (n : ℝ) ^ 2 / e +
      |B * l ^ 2 / e| * n / e ^ 2 + 1 / e ^ 3 ≤
        (B ^ 4 + B ^ 2 / l₀ ^ 3 + 1 / l₀ ^ 6) * l ^ 6 / e ^ 3 := by
  have hlpos : 0 < l := h₀.trans_le hl
  have hβ : 0 ≤ B * l ^ 2 / e := by positivity
  rw [abs_of_nonneg hβ]
  have hn2 : (n : ℝ) ^ 2 ≤ (B * l) ^ 2 := (sq_le_sq₀ (Nat.cast_nonneg _) (by positivity)).mpr hn
  have h3 : l ^ 3 ≤ l ^ 6 / l₀ ^ 3 := by
    apply (le_div_iff₀ (pow_pos h₀ 3)).mpr
    calc
      _ ≤ l ^ 3 * l ^ 3 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h₀.le hl 3) (by positivity)
      _ = _ := by ring
  have h6 : 1 ≤ l ^ 6 / l₀ ^ 6 := (le_div_iff₀ (pow_pos h₀ 6)).mpr (by
    simpa only [one_mul] using pow_le_pow_left₀ h₀.le hl 6)
  calc
    _ ≤ (B * l ^ 2 / e) ^ 2 * (B * l) ^ 2 / e +
        (B * l ^ 2 / e) * (B * l) / e ^ 2 + 1 / e ^ 3 := by
      gcongr
    _ = (B ^ 4 * l ^ 6 + B ^ 2 * l ^ 3 + 1) / e ^ 3 := by ring
    _ ≤ (B ^ 4 * l ^ 6 + B ^ 2 * (l ^ 6 / l₀ ^ 3) + l ^ 6 / l₀ ^ 6) / e ^ 3 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left h3 (sq_nonneg B))) h6
    _ = _ := by ring

lemma exists_gaussian_rectangle_comparison_constants (θ K : ℝ) (hθ : 0 < θ) :
    ∃ B ≥ (1 : ℝ), ∃ C > 0,
      ∀ Q : Finset (Site 2), IsLatticeRectangle Q → 2 ≤ Q.card →
      ∀ (I : Type) [Fintype I] [DecidableEq I],
      ∀ (μ : Measure ℝ), IsProbabilityMeasure μ →
        Integrable (fun x : ℝ => Real.exp (θ * |x|)) μ →
        (∫ x : ℝ, Real.exp (θ * |x|) ∂μ) ≤ K → (∫ x : ℝ, x ∂μ) = 0 →
      ∀ v : ℝ≥0, (∫ x : ℝ, x ^ 2 ∂μ) = v →
      ∀ (W : Q → I → ℝ) (a q : ℝ), 0 ≤ a → 0 ≤ q →
        (∀ z i, |W z i| ≤ a) → (∀ z w y, ∑ i, |W z i * W w i * W y i| ≤ q) →
      ∀ (level error : ℝ), 0 < error → 1 ≤ B * (Real.log Q.card) ^ 2 / error →
        (6 * B ^ 2 * (Real.log Q.card) ^ 3 / error) * a ≤ θ / 2 →
        (Measure.pi (fun _ : I => μ)).real {x | crossingValue Q (linearField W x) ≤ level} ≤
          (Measure.pi (fun _ : I => gaussianReal 0 v)).real
            {x | crossingValue Q (linearField W x) ≤ level + 3 * error} +
          C * (Real.log Q.card) ^ 6 / error ^ 3 * q := by
  classical
  obtain ⟨G, hG, hcompare⟩ := exists_gaussian_sublevel_comparison_constant θ K hθ
  obtain ⟨b, hb, hbottleneck⟩ := exists_positive_rectangle_bottleneck
  let B := max b 1
  let D := B ^ 4 + B ^ 2 / (Real.log 2) ^ 3 + 1 / (Real.log 2) ^ 6
  have hB : 1 ≤ B := le_max_right _ _
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have hbB : b ≤ B := le_max_left _ _
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨B, hB, G * D, mul_pos hG hD, ?_⟩
  intro Q hQ hcard I _ _ μ hμ hexp hK hmean v hsecond W a q ha hq hW hoverlap
    level error herr hβ hκ
  letI : IsProbabilityMeasure μ := hμ
  let l := Real.log Q.card
  let β := B * l ^ 2 / error
  have hl : Real.log 2 ≤ l := Real.log_le_log (by norm_num) (by exact_mod_cast hcard)
  have hlpos : 0 < l := hlog2.trans_le hl
  have hβpos : 0 < β := zero_lt_one.trans_le hβ
  obtain ⟨n, f, hn, ⟨A, hA⟩, hf⟩ := hbottleneck Q hQ hcard β hβ
  have hnB : (n : ℝ) ≤ B * l := hn.trans (mul_le_mul_of_nonneg_right hbB hlpos.le)
  have happ (F : Q → ℝ) : |f F - crossingValue Q F| ≤ error := by
    apply (hf F).trans
    calc
      _ ≤ B * l ^ 2 / β := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hbB (sq_nonneg l)) hβpos.le
      _ = error := by dsimp [β]; field_simp
  have hκ' : (6 * |β| * n) * a ≤ θ / 2 := by
    rw [abs_of_pos hβpos]
    calc
      _ ≤ (6 * β * (B * l)) * a :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnB (by positivity)) ha
      _ = (6 * B ^ 2 * l ^ 3 / error) * a := by dsimp [β]; ring
      _ ≤ _ := hκ
  have hN : Q.Nonempty := Finset.card_pos.mp (by omega)
  have hh := hcompare Q I A β n f (crossingValue Q) hA (measurable_crossingValue hQ hN)
    μ hμ hexp hK hmean v hsecond W a q ha hq hW hoverlap hκ' level error herr happ
  apply hh.trans (add_le_add le_rfl ?_)
  calc
    _ ≤ G * (D * l ^ 6 / error ^ 3) * q :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (rectangle_comparison_scale_le hBpos.le hlog2 hl herr hnB) hG.le) hq
    _ = _ := by ring

lemma exists_gaussian_far_rectangle_comparison_constants
    (hBall : External.BallGreenBounds) (θ K : ℝ) (hθ : 0 < θ) :
    ∃ B ≥ (1 : ℝ), ∃ C > 0, ∃ D > 0,
      ∀ Q : Finset (Site 2), IsLatticeRectangle Q → 2 ≤ Q.card →
      ∀ (r L : ℕ), 2 ≤ r → 2 ≤ L →
      ∀ φ : ℝ → ℝ, External.BallGreen.IsCutoff φ → ∀ z : Q → Site 4,
      ∀ (μ : Measure ℝ), IsProbabilityMeasure μ →
        Integrable (fun x : ℝ => Real.exp (θ * |x|)) μ →
        (∫ x : ℝ, Real.exp (θ * |x|) ∂μ) ≤ K → (∫ x : ℝ, x ∂μ) = 0 →
      ∀ v : ℝ≥0, (∫ x : ℝ, x ^ 2 ∂μ) = v →
      ∀ (level error : ℝ), 0 < error → 1 ≤ B * (Real.log Q.card) ^ 2 / error →
        D * (Real.log Q.card) ^ 3 / (error * (L : ℝ) ^ 2) ≤ θ / 2 →
        (LatticeProb.iidLaw 4 μ).real
          {ζ | crossingValue Q (fun w => finiteKernelField (External.BallGreen.cutField r L φ) ζ (z w)) ≤ level} ≤
        (LatticeProb.iidLaw 4 (gaussianReal 0 v)).real
          {ζ | crossingValue Q (fun w => finiteKernelField (External.BallGreen.cutField r L φ) ζ (z w)) ≤ level + 3 * error} +
          C * (Real.log Q.card) ^ 6 / (error ^ 3 * (L : ℝ) ^ 2) := by
  classical
  obtain ⟨B, hB, C, hC, hcompare⟩ := exists_gaussian_rectangle_comparison_constants θ K hθ
  obtain ⟨H, hH, hcoeff⟩ := cutField_finite_coefficients hBall
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  refine ⟨B, hB, C * H, mul_pos hC hH, 6 * B ^ 2 * H, by positivity, ?_⟩
  intro Q hQ hcard r L hr hL φ hφ z μ hμ hexp hK hmean v hsecond level error herr hβ hκ
  letI : IsProbabilityMeasure μ := hμ
  let h := External.BallGreen.cutField r L φ
  obtain ⟨s, hs⟩ := exists_finiteKernelField_coordinates (boxFinset 0 r)
    (fun u hu => cutField_eq_zero_of_notMem_boxFinset r L φ hu) z
  have hN : Q.Nonempty := Finset.card_pos.mp (by omega)
  have hm := measurable_crossingValue hQ hN
  rw [finiteKernelField_sublevel_measure μ h z s hs _ hm,
    finiteKernelField_sublevel_measure (gaussianReal 0 v) h z s hs _ hm]
  obtain ⟨ha, hoverlap⟩ := hcoeff r hr L hL φ hφ
  have hκ' : (6 * B ^ 2 * (Real.log Q.card) ^ 3 / error) * (H / (L : ℝ) ^ 2) ≤ θ / 2 := by
    convert hκ using 1
    ring
  have hh := hcompare Q hQ hcard s μ hμ hexp hK hmean v hsecond
    (fun w (i : s) => h ((i : Site 4) - z w)) (H / (L : ℝ) ^ 2) (H / (L : ℝ) ^ 2)
    (by positivity) (by positivity) (fun w i => ha _) (fun w y v => hoverlap s (z w) (z y) (z v))
    level error herr hβ hκ'
  convert hh using 1
  ring

end Sandpile
