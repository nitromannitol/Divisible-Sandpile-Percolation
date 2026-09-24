/-
The RSW step: a fixed positive lower bound for the hard-rectangle crossing
probability of the planar image of an iid field, from a half bound for the
easy rectangle containing a square.
-/
import Sandpile.Support.KernelPlanarLaw
import Sandpile.Support.RectangleMonotonicity
import Sandpile.External.PlanarRSW

open MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
namespace Sandpile

/-- The planar image of an iid four-dimensional field under a finite-kernel
cutoff field is a probability measure. -/
lemma isProbabilityMeasure_planar_image (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (r L : ℕ) (φ : ℝ → ℝ) (x : Site 4) :
    IsProbabilityMeasure ((LatticeProb.iidLaw 4 μ).map
      (fun ζ : Site 4 → ℝ => fun z : Site 2 =>
        finiteKernelField (External.BallGreen.cutField r L φ) ζ (planeTranslate x z))) := by
  exact Measure.isProbabilityMeasure_map
    (Measurable.aemeasurable (measurable_pi_lambda _ (fun z =>
    measurable_finiteKernelField (boxFinset 0 r)
      (fun _ hu => cutField_eq_zero_of_notMem_boxFinset r L φ hu) (planeTranslate x z))))

/-- The image measure of a crossing event is the iid measure of its
preimage. -/
lemma planar_image_event (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (r L : ℕ) (φ : ℝ → ℝ) (x : Site 4) (w h : ℕ) (level : ℝ) :
    ((LatticeProb.iidLaw 4 μ).map
      (fun ζ : Site 4 → ℝ => fun z : Site 2 =>
        finiteKernelField (External.BallGreen.cutField r L φ) ζ (planeTranslate x z)))
      (planarCrossingEvent w h level) =
    LatticeProb.iidLaw 4 μ
      {ζ | level ≤ crossingValue (planeRectangle w h) (fun z =>
        finiteKernelField (External.BallGreen.cutField r L φ) ζ (planeTranslate x z))} := by
  rw [Measure.map_apply (measurable_pi_lambda _ (fun z =>
    measurable_finiteKernelField (boxFinset 0 r)
      (fun _ hu => cutField_eq_zero_of_notMem_boxFinset r L φ hu) (planeTranslate x z)))
    (measurableSet_planarCrossingEvent w h level)]
  rfl

/-- The RSW hard-rectangle step: if the easy rectangle `2r x 2ρr` is crossed
at level `-(b log r)` with probability at least one half, then the hard
rectangle `2ρr x 2r` is crossed with probability at least `ψ(1/2) > 0`. -/
lemma rsw_hard_rectangle_lower (hRSW : External.PlanarRSW)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (ρ : ℕ) (hρ : 1 ≤ ρ) :
    ∃ q : ℝ, 0 < q ∧ ∀ (r L : ℕ), 1 ≤ r → ∀ φ : ℝ → ℝ,
    External.BallGreen.IsCutoff φ → ∀ (x : Site 4) (b : ℝ),
    ((1 : ℝ) / 2 ≤ ((LatticeProb.iidLaw 4 μ).map
      (fun ζ : Site 4 → ℝ => fun z : Site 2 =>
        finiteKernelField (External.BallGreen.cutField r L φ) ζ (planeTranslate x z))).real
      (planarCrossingEvent (2 * r) (2 * ρ * r) (-(b * Real.log r)))) →
    q ≤
    ((LatticeProb.iidLaw 4 μ).map
      (fun ζ : Site 4 → ℝ => fun z : Site 2 =>
        finiteKernelField (External.BallGreen.cutField r L φ) ζ (planeTranslate x z))).real
      (planarCrossingEvent (2 * ρ * r) (2 * r) (-(b * Real.log r))) := by
  obtain ⟨ψ, hψ⟩ := hRSW ρ hρ
  set half : Set.Icc (0 : ℝ) 1 := ⟨(1 : ℝ) / 2, by norm_num, by norm_num⟩ with hh
  have hpos : (0 : ℝ) < ((ψ half : Set.Icc (0 : ℝ) 1) : ℝ) := by
    have h1 : (⟨(0 : ℝ), by norm_num, by norm_num⟩ : Set.Icc (0 : ℝ) 1) < half := by
      show ((⟨(0 : ℝ), by norm_num, by norm_num⟩ : Set.Icc (0 : ℝ) 1) : ℝ) < (half : ℝ)
      show (0 : ℝ) < (1 : ℝ) / 2
      norm_num
    have h2 := ψ.strictMono h1
    have h0 : ((ψ (⟨(0 : ℝ), by norm_num, by norm_num⟩ : Set.Icc (0 : ℝ) 1)) : ℝ) = 0 := by
      have hb : (⟨(0 : ℝ), by norm_num, by norm_num⟩ : Set.Icc (0 : ℝ) 1) = ⊥ := rfl
      have hb2 := congrArg ψ hb
      simp only [OrderIso.map_bot] at hb2
      simp only [hb2]
      norm_num
    have h2' : ((ψ (⟨(0 : ℝ), by norm_num, by norm_num⟩ : Set.Icc (0 : ℝ) 1)) : ℝ) <
        ((ψ half : Set.Icc (0 : ℝ) 1) : ℝ) :=
      Subtype.coe_lt_coe.mpr (by simpa using h2)
    rw [h0] at h2'
    exact h2'
  refine ⟨((ψ half : Set.Icc (0 : ℝ) 1) : ℝ), hpos, ?_⟩
  intro r L hr φ hφ x b heasy
  haveI : IsProbabilityMeasure ((LatticeProb.iidLaw 4 μ).map
      (fun ζ : Site 4 → ℝ => fun z : Site 2 =>
        finiteKernelField (External.BallGreen.cutField r L φ) ζ (planeTranslate x z))) :=
    isProbabilityMeasure_planar_image μ r L φ x
  have hRSW' := hψ _ (isSymmetricPlanarLaw_cutField μ r L φ x)
    (isAssociatedPlanarLaw_cutField μ r L hφ x) r hr (-(b * Real.log r))
  have hhalf : half ≤
      probabilityInUnitInterval ((LatticeProb.iidLaw 4 μ).map
        (fun ζ : Site 4 → ℝ => fun z : Site 2 =>
          finiteKernelField (External.BallGreen.cutField r L φ) ζ (planeTranslate x z)))
        (planarCrossingEvent (2 * r) (2 * ρ * r) (-(b * Real.log r))) := by
    simp only [probabilityInUnitInterval]
    exact heasy
  set peasy : Set.Icc (0 : ℝ) 1 :=
    probabilityInUnitInterval ((LatticeProb.iidLaw 4 μ).map
      (fun ζ : Site 4 → ℝ => fun z : Site 2 =>
        finiteKernelField (External.BallGreen.cutField r L φ) ζ (planeTranslate x z)))
      (planarCrossingEvent (2 * r) (2 * ρ * r) (-(b * Real.log r))) with hpe
  have hq : ψ half ≤ ψ peasy := ψ.monotone hhalf
  have h1 : ((ψ half : Set.Icc (0 : ℝ) 1) : ℝ) ≤ ((ψ peasy : Set.Icc (0 : ℝ) 1) : ℝ) :=
    Subtype.coe_le_coe.mpr hq
  exact h1.trans hRSW'

end Sandpile
end
