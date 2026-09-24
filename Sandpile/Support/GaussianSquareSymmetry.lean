/-
The horizontal-vertical expectation identity and integrability of Gaussian far-field crossing values.
-/
import Sandpile.Support.KernelSymmetry
import Sandpile.Support.RectangleTranspose
import Sandpile.Support.GaussianBottleneck

open MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
namespace Sandpile

lemma affinePermuteSite_swap_plane (x : Site 4) (z : Site 2) :
    affinePermuteSite (Equiv.swap (0 : Fin 4) 1) x (planeTranslate x z) =
      planeTranslate x (permuteSite (Equiv.swap (0 : Fin 2) 1) z) := by
  ext i
  change x i + ((planeTranslate x z) ((Equiv.swap (0 : Fin 4) 1) i) -
    x ((Equiv.swap (0 : Fin 4) 1) i)) = (planeTranslate x (permuteSite (Equiv.swap (0 : Fin 2) 1) z)) i
  fin_cases i <;> norm_num [Equiv.swap_apply_def, planeTranslate, permuteSite]

lemma integral_vertical_gaussian_far_eq_horizontal (r L s : ℕ) (φ : ℝ → ℝ)
    (x : Site 4) (v : ℝ≥0) :
    (∫ ζ : Site 4 → ℝ, verticalCrossingValue s s (fun z =>
      -finiteKernelField (External.BallGreen.cutField r L φ) ζ (planeTranslate x z))
        ∂LatticeProb.iidLaw 4 (gaussianReal 0 v)) =
    ∫ ζ : Site 4 → ℝ, crossingValue (planeRectangle s s) (fun z =>
      finiteKernelField (External.BallGreen.cutField r L φ) ζ (planeTranslate x z))
        ∂LatticeProb.iidLaw 4 (gaussianReal 0 v) := by
  have hh := integral_finiteKernel_affine_permute_neg (Equiv.swap (0 : Fin 4) 1) x
    (External.BallGreen.cutField r L φ) (cutField_permute _ r L φ) (boxFinset 0 r)
    (fun u hu => cutField_eq_zero_of_notMem_boxFinset r L φ hu)
    (fun z : planeRectangle s s => planeTranslate x z) (crossingValue (planeRectangle s s))
    (measurable_crossingValue (isLatticeRectangle_planeRectangle s s) (planeRectangle_nonempty s s)) v
  change (∫ ζ : Site 4 → ℝ, crossingValue (planeRectangle s s) (fun z =>
    -finiteKernelField (External.BallGreen.cutField r L φ) ζ
      (planeTranslate x (permuteSite (Equiv.swap (0 : Fin 2) 1) z)))
        ∂LatticeProb.iidLaw 4 (gaussianReal 0 v)) = _
  simpa only [affinePermuteSite_swap_plane] using hh

lemma integrable_gaussian_finiteKernel_crossing {Q : Finset (Site 2)}
    (hQ : IsLatticeRectangle Q) (hN : 2 ≤ Q.card) {d : ℕ} {h : Site d → ℝ}
    (t : Finset (Site d)) (ht : ∀ u ∉ t, h u = 0) (z : Q → Site d) (v : ℝ≥0) :
    Integrable (fun ζ : Site d → ℝ => crossingValue Q (fun w => finiteKernelField h ζ (z w)))
      (LatticeProb.iidLaw d (gaussianReal 0 v)) := by
  have hs : Summable (fun u => h u ^ 2) :=
    summable_of_ne_finset_zero (s := t) (fun u hu => by rw [ht u hu, zero_pow (by decide : 2 ≠ 0)])
  have hn : 0 ≤ (v : ℝ) * (∑' u, h u ^ 2) := mul_nonneg v.coe_nonneg (tsum_nonneg (fun _ => sq_nonneg _))
  let D : ℝ≥0 := ⟨Real.sqrt ((v : ℝ) * (∑' u, h u ^ 2)), Real.sqrt_nonneg _⟩
  have hD : (v : ℝ) * (∑' u, h u ^ 2) ≤ (D : ℝ) ^ 2 := by
    change (v : ℝ) * (∑' u, h u ^ 2) ≤ Real.sqrt ((v : ℝ) * (∑' u, h u ^ 2)) ^ 2
    rw [Real.sq_sqrt hn]
  have hh := hasSubgaussianMGF_finiteKernel_crossing hQ hN t ht hs z v D hD
  have hi := hh.integrable.add (integrable_const (∫ ζ : Site d → ℝ,
    crossingValue Q (fun w => finiteKernelField h ζ (z w)) ∂LatticeProb.iidLaw d (gaussianReal 0 v)))
  exact hi.congr (Filter.Eventually.of_forall (fun ζ => sub_add_cancel _ _))

lemma integrable_gaussian_far_crossing {Q : Finset (Site 2)}
    (hQ : IsLatticeRectangle Q) (hN : 2 ≤ Q.card) (r L : ℕ) (φ : ℝ → ℝ)
    (z : Q → Site 4) (v : ℝ≥0) :
    Integrable (fun ζ : Site 4 → ℝ => crossingValue Q
      (fun w => finiteKernelField (External.BallGreen.cutField r L φ) ζ (z w)))
      (LatticeProb.iidLaw 4 (gaussianReal 0 v)) :=
  integrable_gaussian_finiteKernel_crossing hQ hN (boxFinset 0 r)
    (fun _ hu => cutField_eq_zero_of_notMem_boxFinset r L φ hu) z v

end Sandpile
