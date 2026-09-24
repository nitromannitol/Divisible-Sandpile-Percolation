/-
Spatial symmetries and positive association of planar finite-kernel iid fields.
-/
import Sandpile.Support.KernelReflection
import Sandpile.Support.PlanarLaw
import Sandpile.Support.GaussianSquareSymmetry

open MeasureTheory ProbabilityTheory
noncomputable section
namespace Sandpile

def affineAddSite {d : ℕ} (e : Site d ≃+ Site d) (x : Site d) : Site d ≃ Site d :=
  (Equiv.subRight x).trans (e.toEquiv.trans (Equiv.addLeft x))

lemma affineAddSite_apply {d : ℕ} (e : Site d ≃+ Site d) (x y : Site d) :
    affineAddSite e x y = x + e (y - x) := rfl

lemma finiteKernelField_affine_addEquiv {d : ℕ} (e : Site d ≃+ Site d) (x : Site d)
    (h : Site d → ℝ) (hh : ∀ u, h (e u) = h u) (ζ : Site d → ℝ) (z : Site d) :
    finiteKernelField h (fun y => ζ (affineAddSite e x y)) z =
      finiteKernelField h ζ (affineAddSite e x z) := by
  unfold finiteKernelField
  have he (u : Site d) : affineAddSite e x (z + u) = affineAddSite e x z + e u := by
    simp only [affineAddSite_apply]
    rw [show z + u - x = z - x + u by abel, map_add, add_assoc]
  calc
    _ = ∑' u : Site d, h (e u) * ζ (affineAddSite e x z + e u) := tsum_congr (fun u => by
      change h u * ζ (affineAddSite e x (z + u)) = _
      rw [hh, he])
    _ = _ := e.toEquiv.tsum_eq (fun u => h u * ζ (affineAddSite e x z + u))

lemma finiteKernelField_translate {d : ℕ} (h : Site d → ℝ) (ζ : Site d → ℝ) (v z : Site d) :
    finiteKernelField h (fun y => ζ (y + v)) z = finiteKernelField h ζ (z + v) := by
  unfold finiteKernelField
  apply tsum_congr
  intro u
  change h u * ζ (z + u + v) = h u * ζ (z + v + u)
  rw [show z + u + v = z + v + u by abel]

lemma planeTranslate_add (x : Site 4) (z v : Site 2) :
    planeTranslate x (z + v) = planeTranslate x z + planeTranslate 0 v := by
  ext i
  fin_cases i <;> simp [planeTranslate, add_assoc]

lemma affineAddSite_reflect_plane (x : Site 4) (z : Site 2) :
    affineAddSite (reflectSite (0 : Fin 4)) x (planeTranslate x z) =
      planeTranslate x ![-z 0, z 1] := by
  ext i
  fin_cases i
  · change x 0 + -((x 0 + z 0) - x 0) = x 0 + -z 0
    ring
  · change x 1 + ((x 1 + z 1) - x 1) = x 1 + z 1
    ring
  · change x 2 + (x 2 - x 2) = x 2
    ring
  · change x 3 + (x 3 - x 3) = x 3
    ring

lemma measurePreserving_map_factor {Ω Λ : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ]
    {μ : Measure Ω} {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    (H : Ω → Λ) (hH : Measurable H) (S : Λ → Λ) (hS : Measurable S)
    (he : ∀ ω, S (H ω) = H (T ω)) : MeasurePreserving S (μ.map H) (μ.map H) := by
  refine ⟨hS, ?_⟩
  rw [Measure.map_map hS hH, show S ∘ H = H ∘ T from funext he,
    ← Measure.map_map hH hT.measurable, hT.map_eq]

lemma isSymmetricPlanarLaw_cutField (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (r L : ℕ) (φ : ℝ → ℝ) (x : Site 4) :
    IsSymmetricPlanarLaw ((LatticeProb.iidLaw 4 μ).map
      (fun ζ : Site 4 → ℝ => fun z : Site 2 =>
        finiteKernelField (External.BallGreen.cutField r L φ) ζ (planeTranslate x z))) := by
  let h := External.BallGreen.cutField r L φ
  let H (ζ : Site 4 → ℝ) (z : Site 2) := finiteKernelField h ζ (planeTranslate x z)
  have hH : Measurable H := measurable_pi_lambda _ (fun z =>
    measurable_finiteKernelField (boxFinset 0 r)
      (fun _ hu => cutField_eq_zero_of_notMem_boxFinset r L φ hu) (planeTranslate x z))
  refine ⟨?_, ?_, ?_⟩
  · intro v
    apply measurePreserving_map_factor
      (measurePreserving_iid_reindex μ (Equiv.addRight (planeTranslate 0 v))) H hH (planarFieldShift v)
      (measurable_pi_lambda _ (fun z => measurable_pi_apply (z + v)))
    intro ζ
    funext z
    change finiteKernelField h ζ (planeTranslate x (z + v)) =
      finiteKernelField h (fun y => ζ (y + planeTranslate 0 v)) (planeTranslate x z)
    rw [finiteKernelField_translate, planeTranslate_add]
  · apply measurePreserving_map_factor
      (measurePreserving_iid_reindex μ (affinePermuteSite (Equiv.swap (0 : Fin 4) 1) x)) H hH
      planarFieldTranspose (measurable_pi_lambda _ (fun z => measurable_pi_apply ![z 1, z 0]))
    intro ζ
    funext z
    change finiteKernelField h ζ (planeTranslate x ![z 1, z 0]) =
      finiteKernelField h (fun y => ζ (affinePermuteSite (Equiv.swap (0 : Fin 4) 1) x y)) (planeTranslate x z)
    rw [finiteKernelField_affine_permute _ x h (cutField_permute _ r L φ),
      affinePermuteSite_swap_plane, permuteSite_swap_plane]
  · apply measurePreserving_map_factor
      (measurePreserving_iid_reindex μ (affineAddSite (reflectSite (0 : Fin 4)) x)) H hH
      planarFieldReflect (measurable_pi_lambda _ (fun z => measurable_pi_apply ![-z 0, z 1]))
    intro ζ
    funext z
    change finiteKernelField h ζ (planeTranslate x ![-z 0, z 1]) =
      finiteKernelField h (fun y => ζ (affineAddSite (reflectSite (0 : Fin 4)) x y)) (planeTranslate x z)
    rw [finiteKernelField_affine_addEquiv _ x h (cutField_reflect _ r L φ), affineAddSite_reflect_plane]

lemma isAssociatedPlanarLaw_cutField (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (r L : ℕ) {φ : ℝ → ℝ} (hφ : External.BallGreen.IsCutoff φ) (x : Site 4) :
    IsAssociatedPlanarLaw ((LatticeProb.iidLaw 4 μ).map
      (fun ζ : Site 4 → ℝ => fun z : Site 2 =>
        finiteKernelField (External.BallGreen.cutField r L φ) ζ (planeTranslate x z))) :=
  isAssociatedPlanarLaw_finiteKernel μ (boxFinset 0 r)
    (fun _ hu => cutField_eq_zero_of_notMem_boxFinset r L φ hu) (cutField_nonneg r L hφ) x

end Sandpile
