import Sandpile.External.Stopping.CenteredWalkDecode
import Sandpile.External.Stopping.WalkBrownianInvariance
import LatticeProb.Walk.Range

/-!
# Law of the centered interpolated walk

Centering the diffusively rescaled walk at its lattice starting point removes
the dependence of its path law on that point. The centered path laws converge
to Brownian motion started at the origin.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace Sandpile.External.Stopping

/-- Centered interpolations driven by the same increments coincide for any two
lattice starting points. -/
theorem centeredWalkPath_sitePath_eq {d : ℕ} (R : ℝ) (q : Site d)
    (ξ : ℕ → Site d) :
    centeredWalkPath R q (LatticeProb.sitePath q ξ) =
      centeredWalkPath R 0 (LatticeProb.sitePath 0 ξ) := by
  apply ContinuousMap.ext
  intro t
  change diffusiveWalk R t (LatticeProb.sitePath q ξ) - Lclt.scaledSite R q =
    diffusiveWalk R t (LatticeProb.sitePath 0 ξ) - Lclt.scaledSite R 0
  rw [← centered_constantStep_path_eq_diffusiveWalk,
    ← centered_constantStep_path_eq_diffusiveWalk]
  have hp : centeredScaledSite R q ∘ LatticeProb.sitePath q ξ =
      centeredScaledSite R 0 ∘ LatticeProb.sitePath 0 ξ := by
    funext k
    simp only [Function.comp_apply, centeredScaledSite, sub_zero]
    congr 1
    simpa only [sub_self] using (LatticeProb.sitePath_sub q q ξ k).symm
  rw [hp]

/-- The centered path from the origin is the diffusively interpolated walk. -/
theorem centeredWalkPath_zero {d : ℕ} (R : ℝ) (X : ℕ → Site d) :
    centeredWalkPath R 0 X = diffusiveWalkPath R X := by
  apply ContinuousMap.ext
  intro t
  change diffusiveWalk R t X - Lclt.scaledSite R 0 = diffusiveWalk R t X
  have hzero : Lclt.scaledSite R (0 : Site d) = 0 := by
    ext i
    simp [Lclt.scaledSite]
  rw [hzero, sub_zero]

/-- The centered path law is independent of the initial lattice point. -/
theorem map_centeredWalkPath_eq {d : ℕ} [NeZero d] (R : ℝ) (q : Site d) :
    (walkLaw d q).map (centeredWalkPath R q) =
      (walkLaw d 0).map (diffusiveWalkPath R) := by
  change (LatticeProb.siteWalkLaw d q).map (centeredWalkPath R q) =
    (LatticeProb.siteWalkLaw d 0).map (diffusiveWalkPath R)
  rw [LatticeProb.siteWalkLaw_eq, LatticeProb.siteWalkLaw_eq,
    Measure.map_map (measurable_centeredWalkPath R q) (LatticeProb.measurable_sitePath q),
    Measure.map_map (measurable_diffusiveWalkPath R) (LatticeProb.measurable_sitePath 0)]
  congr 1
  funext ξ
  simpa only [Function.comp_apply, centeredWalkPath_zero] using centeredWalkPath_sitePath_eq R q ξ

/-- The probability law of a centered interpolated walk. -/
noncomputable def centeredWalkPathLaw (d : ℕ) [NeZero d] (R : ℝ) (q : Site d) :
    ProbabilityMeasure C(ℝ≥0, Continuum.Space d) :=
  ⟨(walkLaw d q).map (centeredWalkPath R q),
    (Measure.isProbabilityMeasure_map_iff (measurable_centeredWalkPath R q).aemeasurable).2
      (by change IsProbabilityMeasure (LatticeProb.siteWalkLaw d q); infer_instance)⟩

/-- Centered path laws converge weakly to a measurable continuous Brownian
version, for every sequence of lattice starting points. -/
theorem exists_centered_brownian_path_limit
    (d : ℕ) [NeZero d] (R : ℕ → ℝ) (q : ℕ → Site d) (hR : Tendsto R atTop atTop)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → Continuum.Space d) (hB : LatticeProb.IsBrownianSpace d 0 B P) :
    ∃ (F : Ω → C(ℝ≥0, Continuum.Space d)) (hFm : Measurable F),
      (∀ᵐ ω ∂P, ∀ t, F ω t = B t ω) ∧
      Tendsto (fun n => centeredWalkPathLaw d (R n) (q n)) atTop
        (𝓝 (⟨P.map F, (Measure.isProbabilityMeasure_map_iff hFm.aemeasurable).2 inferInstance⟩ :
          ProbabilityMeasure C(ℝ≥0, Continuum.Space d))) := by
  have hstart : Tendsto (fun n : ℕ => Lclt.scaledSite (R n) (0 : Site d)) atTop (𝓝 0) := by
    have hz (n : ℕ) : Lclt.scaledSite (R n) (0 : Site d) = 0 := by
      ext i
      simp [Lclt.scaledSite]
    simpa only [hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : Continuum.Space d)) atTop (𝓝 0))
  obtain ⟨F, hFm, hF, hlim⟩ := exists_brownian_path_limit d R (fun _ => 0) hR 0 hstart P B hB
  refine ⟨F, hFm, ?_, ?_⟩
  · filter_upwards [hF] with ω hω t
    simpa only [zero_add] using hω t
  · have heq (n : ℕ) : centeredWalkPathLaw d (R n) (q n) =
        diffusiveWalkPathLaw d (R n) 0 := by
      apply ProbabilityMeasure.toMeasure_injective
      exact map_centeredWalkPath_eq (R n) (q n)
    simpa only [heq] using hlim

end Sandpile.External.Stopping
