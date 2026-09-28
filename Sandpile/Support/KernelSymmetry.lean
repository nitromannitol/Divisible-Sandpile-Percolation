import Sandpile.Support.KernelPermutation
import Sandpile.Support.CrossingContinuity
import LatticeProb.Prob.MapPi
import LatticeProb.Prob.ZeroOne

/-!
# Affine coordinate symmetries of finite-kernel fields, and sign reversal of the Gaussian law

`finiteKernelField h ζ z = ∑' u, h u * ζ (z + u)` is equivariant under any affine map built from a
coordinate permutation `e` and a translation by `x`, `affinePermuteSite e x`, provided the weight
`h` is itself `e`-invariant (`finiteKernelField_affine_permute`), and it changes sign when the
noise `ζ` does (`finiteKernelField_neg`). Reindexing the noise coordinates by an equivalence of
`Site d`, or negating it, each preserve the i.i.d. Gaussian law
(`measurePreserving_iid_reindex`, `measurePreserving_iid_gaussian_neg`, and their composite
`measurePreserving_iid_gaussian_neg_reindex`). Combining these symmetries with measurability of
`finiteKernelField` in the noise (`measurable_finiteKernelField`) gives the main tool
(`integral_finiteKernel_affine_permute_neg`): a Gaussian integral of any measurable functional of
the field is unchanged under simultaneously permuting/translating the base point and negating the
field.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
namespace Sandpile

/-- The affine bijection of `Site d` about base point `x` built from a coordinate permutation
`e`: translate by `-x`, permute via `permuteSite e`, then translate back by `x`. -/
def affinePermuteSite {d : ℕ} (e : Fin d ≃ Fin d) (x : Site d) : Site d ≃ Site d :=
  (Equiv.subRight x).trans ((permuteSite e).toEquiv.trans (Equiv.addLeft x))

/-- Unfolds `affinePermuteSite e x y` as `x + permuteSite e (y - x)`. -/
lemma affinePermuteSite_apply {d : ℕ} (e : Fin d ≃ Fin d) (x y : Site d) :
    affinePermuteSite e x y = x + permuteSite e (y - x) := rfl

/-- If the weight `h` is invariant under `permuteSite e`, then `finiteKernelField` is equivariant
under precomposing the noise with `affinePermuteSite e x`: evaluating at `z` after warping the
noise by the affine map agrees with evaluating the unwarped field at the warped point
`affinePermuteSite e x z`. -/
lemma finiteKernelField_affine_permute {d : ℕ} (e : Fin d ≃ Fin d) (x : Site d)
    (h : Site d → ℝ) (hh : ∀ u, h (permuteSite e u) = h u) (ζ : Site d → ℝ) (z : Site d) :
    finiteKernelField h (fun y => ζ (affinePermuteSite e x y)) z =
      finiteKernelField h ζ (affinePermuteSite e x z) := by
  unfold finiteKernelField
  have he (u : Site d) : affinePermuteSite e x (z + u) =
      affinePermuteSite e x z + permuteSite e u := by
    simp only [affinePermuteSite_apply]
    rw [show z + u - x = z - x + u by abel, map_add, add_assoc]
  calc
    _ = ∑' u : Site d, h (permuteSite e u) *
        ζ (affinePermuteSite e x z + permuteSite e u) := tsum_congr (fun u => by
          change h u * ζ (affinePermuteSite e x (z + u)) = _
          rw [hh, he])
    _ = _ := (permuteSite e).toEquiv.tsum_eq (fun u => h u * ζ (affinePermuteSite e x z + u))

/-- `finiteKernelField` is linear (odd) in the noise: negating `ζ` negates the field's value. -/
lemma finiteKernelField_neg {d : ℕ} (h : Site d → ℝ) (ζ : Site d → ℝ) (z : Site d) :
    finiteKernelField h (fun y => -ζ y) z = -finiteKernelField h ζ z := by
  simp only [finiteKernelField, mul_neg, tsum_neg]

/-- `finiteKernelField h · z` is measurable in the noise `ζ`, given a finite set `t` outside of
which the weight `h` vanishes, via the finite-sum representation `finiteKernelField_eq_sum`. -/
lemma measurable_finiteKernelField {d : ℕ} {h : Site d → ℝ}
    (t : Finset (Site d)) (ht : ∀ u ∉ t, h u = 0) (z : Site d) :
    Measurable (fun ζ : Site d → ℝ => finiteKernelField h ζ z) := by
  simp only [finiteKernelField_eq_sum t ht]
  exact Finset.measurable_sum _ (fun u _ => measurable_const.mul (measurable_pi_apply (z + u)))

/-- Reindexing the coordinates of an i.i.d. field by an equivalence `e` of `Site d` preserves the
i.i.d. law `LatticeProb.iidLaw d μ`, since the coordinates are exchangeable. -/
lemma measurePreserving_iid_reindex {d : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (e : Site d ≃ Site d) :
    MeasurePreserving (fun ζ : Site d → ℝ => fun y => ζ (e y))
      (LatticeProb.iidLaw d μ) (LatticeProb.iidLaw d μ) :=
  LatticeProb.measurePreserving_coordShift (fun _ : Site d => μ) e.injective (fun _ => rfl)

/-- Negating an i.i.d. centered-Gaussian field preserves its law, since `gaussianReal 0 v` is
symmetric about `0`. -/
lemma measurePreserving_iid_gaussian_neg (d : ℕ) (v : ℝ≥0) :
    MeasurePreserving (fun ζ : Site d → ℝ => fun y => -ζ y)
      (LatticeProb.iidLaw d (gaussianReal 0 v)) (LatticeProb.iidLaw d (gaussianReal 0 v)) := by
  refine ⟨measurable_pi_lambda _ (fun y => (measurable_pi_apply y).neg), ?_⟩
  rw [LatticeProb.iidLaw_map_pi d (gaussianReal 0 v)
      (show Measurable (fun x : ℝ => -x) by fun_prop),
    gaussianReal_map_neg, neg_zero]

/-- Combining `measurePreserving_iid_gaussian_neg` with `measurePreserving_iid_reindex` along
`e`: negating and reindexing an i.i.d. centered-Gaussian field by `e` preserves its law. -/
lemma measurePreserving_iid_gaussian_neg_reindex {d : ℕ} (v : ℝ≥0) (e : Site d ≃ Site d) :
    MeasurePreserving (fun ζ : Site d → ℝ => fun y => -ζ (e y))
      (LatticeProb.iidLaw d (gaussianReal 0 v)) (LatticeProb.iidLaw d (gaussianReal 0 v)) :=
  (measurePreserving_iid_gaussian_neg d v).comp (measurePreserving_iid_reindex (gaussianReal 0 v) e)

/-- **The main symmetry tool.** For an `e`-invariant, finitely supported weight `h`, a Gaussian
integral of a measurable functional `value` of the negated, affinely-warped field
`finiteKernelField h ζ (affinePermuteSite e x (z q))` equals the same integral of the unwarped
field `finiteKernelField h ζ (z q)`, obtained by pushing the measure-preserving map
`measurePreserving_iid_gaussian_neg_reindex` through the change-of-variables identity
`integral_map`. -/
lemma integral_finiteKernel_affine_permute_neg {d : ℕ} {V : Type*}
    (e : Fin d ≃ Fin d) (x : Site d) (h : Site d → ℝ)
    (hh : ∀ u, h (permuteSite e u) = h u)
    (t : Finset (Site d)) (ht : ∀ u ∉ t, h u = 0)
    (z : V → Site d) (value : (V → ℝ) → ℝ) (hv : Measurable value) (v : ℝ≥0) :
    (∫ ζ : Site d → ℝ, value (fun q => -finiteKernelField h ζ (affinePermuteSite e x (z q)))
      ∂LatticeProb.iidLaw d (gaussianReal 0 v)) =
    ∫ ζ : Site d → ℝ, value (fun q => finiteKernelField h ζ (z q))
      ∂LatticeProb.iidLaw d (gaussianReal 0 v) := by
  let T (ζ : Site d → ℝ) (y : Site d) := -ζ (affinePermuteSite e x y)
  let f (ζ : Site d → ℝ) := value (fun q => finiteKernelField h ζ (z q))
  have hT := measurePreserving_iid_gaussian_neg_reindex v (affinePermuteSite e x)
  have hf : Measurable f :=
    hv.comp (measurable_pi_lambda _ (fun q => measurable_finiteKernelField t ht (z q)))
  have he (ζ : Site d → ℝ) : f (T ζ) =
      value (fun q => -finiteKernelField h ζ (affinePermuteSite e x (z q))) := by
    dsimp [f, T]
    congr 1
    funext q
    rw [finiteKernelField_neg, finiteKernelField_affine_permute e x h hh]
  have hi := integral_map hT.aemeasurable hf.aestronglyMeasurable
  rw [hT.map_eq] at hi
  simpa only [Function.comp_def, he, f, T] using hi.symm

end Sandpile
