import Sandpile.Support.KernelSymmetry
import Sandpile.Support.RectangleTranspose
import Sandpile.Support.GaussianBottleneck

/-!
# Horizontal-vertical symmetry and integrability of Gaussian far-field crossing values

The horizontal-vertical expectation identity and integrability of Gaussian far-field crossing
values. `integral_vertical_gaussian_far_eq_horizontal` transports the affine swap symmetry of the
far Green field (`integral_finiteKernel_affine_permute_neg`) to identify the expected vertical
crossing value of the negated field with the expected horizontal crossing value of the field
itself; `integrable_gaussian_finiteKernel_crossing` and `integrable_gaussian_far_crossing` record
integrability of the crossing value from its subgaussian MGF.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
namespace Sandpile

/-- **The swap of the first two axes commutes with `planeTranslate`.** Conjugating the affine
permutation of `Site 4` by the swap of coordinates `0` and `1` at a translated point `planeTranslate
x z` agrees with translating `x` by the swap of `z`'s own two coordinates. -/
lemma affinePermuteSite_swap_plane (x : Site 4) (z : Site 2) :
    affinePermuteSite (Equiv.swap (0 : Fin 4) 1) x (planeTranslate x z) =
      planeTranslate x (permuteSite (Equiv.swap (0 : Fin 2) 1) z) := by
  ext i
  change x i + ((planeTranslate x z) ((Equiv.swap (0 : Fin 4) 1) i) -
    x ((Equiv.swap (0 : Fin 4) 1) i)) =
      (planeTranslate x (permuteSite (Equiv.swap (0 : Fin 2) 1) z)) i
  fin_cases i <;> norm_num [Equiv.swap_apply_def, planeTranslate, permuteSite]

/-- **The expected vertical crossing value of the negated far field equals the expected
horizontal crossing value of the field itself.** Transports the affine swap symmetry
`integral_finiteKernel_affine_permute_neg` of the far Green field along
`affinePermuteSite_swap_plane`, using that swapping the two axes of `planeRectangle s s` turns a
vertical crossing into a horizontal one. -/
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
    (measurable_crossingValue (isLatticeRectangle_planeRectangle s s)
      (planeRectangle_nonempty s s)) v
  change (∫ ζ : Site 4 → ℝ, crossingValue (planeRectangle s s) (fun z =>
    -finiteKernelField (External.BallGreen.cutField r L φ) ζ
      (planeTranslate x (permuteSite (Equiv.swap (0 : Fin 2) 1) z)))
        ∂LatticeProb.iidLaw 4 (gaussianReal 0 v)) = _
  simpa only [affinePermuteSite_swap_plane] using hh

/-- **The crossing value of a finitely-supported field against iid Gaussian scenery is
integrable.** Its subgaussian MGF (`hasSubgaussianMGF_finiteKernel_crossing`) gives
integrability of the centered value, and adding back the constant mean recovers integrability of
the value itself. -/
lemma integrable_gaussian_finiteKernel_crossing {Q : Finset (Site 2)}
    (hQ : IsLatticeRectangle Q) (hN : 2 ≤ Q.card) {d : ℕ} {h : Site d → ℝ}
    (t : Finset (Site d)) (ht : ∀ u ∉ t, h u = 0) (z : Q → Site d) (v : ℝ≥0) :
    Integrable (fun ζ : Site d → ℝ => crossingValue Q (fun w => finiteKernelField h ζ (z w)))
      (LatticeProb.iidLaw d (gaussianReal 0 v)) := by
  have hs : Summable (fun u => h u ^ 2) :=
    summable_of_ne_finset_zero (s := t) (fun u hu => by rw [ht u hu, zero_pow (by decide : 2 ≠ 0)])
  have hn : 0 ≤ (v : ℝ) * (∑' u, h u ^ 2) :=
    mul_nonneg v.coe_nonneg (tsum_nonneg (fun _ => sq_nonneg _))
  let D : ℝ≥0 := ⟨Real.sqrt ((v : ℝ) * (∑' u, h u ^ 2)), Real.sqrt_nonneg _⟩
  have hD : (v : ℝ) * (∑' u, h u ^ 2) ≤ (D : ℝ) ^ 2 := by
    change (v : ℝ) * (∑' u, h u ^ 2) ≤ Real.sqrt ((v : ℝ) * (∑' u, h u ^ 2)) ^ 2
    rw [Real.sq_sqrt hn]
  have hh := hasSubgaussianMGF_finiteKernel_crossing hQ hN t ht hs z v D hD
  have hi := hh.integrable.add (integrable_const (∫ ζ : Site d → ℝ,
    crossingValue Q (fun w => finiteKernelField h ζ (z w))
      ∂LatticeProb.iidLaw d (gaussianReal 0 v)))
  exact hi.congr (Filter.Eventually.of_forall (fun ζ => sub_add_cancel _ _))

/-- The far Green field's crossing value against iid Gaussian scenery is integrable: the
finitely-supported case `integrable_gaussian_finiteKernel_crossing`, applied with `t = boxFinset 0
r` since `finiteKernelField (cutField r L φ)` vanishes outside that box. -/
lemma integrable_gaussian_far_crossing {Q : Finset (Site 2)}
    (hQ : IsLatticeRectangle Q) (hN : 2 ≤ Q.card) (r L : ℕ) (φ : ℝ → ℝ)
    (z : Q → Site 4) (v : ℝ≥0) :
    Integrable (fun ζ : Site 4 → ℝ => crossingValue Q
      (fun w => finiteKernelField (External.BallGreen.cutField r L φ) ζ (z w)))
      (LatticeProb.iidLaw 4 (gaussianReal 0 v)) :=
  integrable_gaussian_finiteKernel_crossing hQ hN (boxFinset 0 r)
    (fun _ hu => cutField_eq_zero_of_notMem_boxFinset r L φ hu) z v

end Sandpile
