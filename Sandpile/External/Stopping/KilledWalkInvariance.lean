import Sandpile.External.Stopping.CubeStoppedClock

/-!
# Invariance principle for cube-stopped walks

The centered simple random walk stopped at the lattice cube exit converges in
distribution to Brownian motion stopped at the unit-cube exit. Horizons may
vary and converge. This is the stopped-walk invariance ingredient used in the
optimal-stopping stability argument.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- Centered cube-stopped walk paths converge in distribution to the
corresponding stopped Brownian path, for arbitrary lattice centers and
convergent horizons. -/
theorem tendstoInDistribution_cubeStoppedWalk
    (d : ℕ) [NeZero d] (R : ℕ → ℝ) (q : ℕ → Site d)
    (hRpos : ∀ n, 0 < R n) (hR : Tendsto R atTop atTop)
    (H : ℕ → ℝ≥0) (h : ℝ≥0) (hH : Tendsto H atTop (𝓝 h))
    {ΩB : Type*} [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (B : ℝ≥0 → ΩB → Continuum.Space d) (hB : LatticeProb.IsBrownianSpace d 0 B PB) :
    ∃ (F : ΩB → C(ℝ≥0, Continuum.Space d)) (_hFm : Measurable F),
      (∀ᵐ ω ∂PB, ∀ t, F ω t = B t ω) ∧
      TendstoInDistribution (fun n => cubeStoppedWalk (R n) (hRpos n) (q n) (H n)) atTop
        (fun ω => cubeStoppedPath h (F ω)) (fun n => LatticeProb.siteWalkLaw d (q n)) PB := by
  obtain ⟨F, hFm, hF, Ω, mΩ, P, hP, X, Y, hXm, hYm, hXmap, hYmap, hconv⟩ :=
    exists_cube_stopped_walk_brownian_coupling d R q hRpos hR H h hH PB B hB
  let Z : ℕ → Ω → C(ℝ≥0, Continuum.Space d) :=
    fun n ω => cubeStoppedWalk (R n) (hRpos n) (q n) (H n) (X n ω)
  let Z₀ : Ω → C(ℝ≥0, Continuum.Space d) := fun ω => cubeStoppedPath h (Y ω)
  have hZm (n : ℕ) : Measurable (Z n) :=
    (measurable_cubeStoppedWalk (R n) (hRpos n) (q n) (H n)).comp (hXm n)
  have hZ₀m : Measurable Z₀ := (measurable_cubeStoppedPath h).comp hYm
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => Z n ω) atTop (𝓝 (Z₀ ω)) := by
    filter_upwards [hconv] with ω hw
    dsimp only at hw
    have hz : (fun n => Z n ω) = fun n => LatticeProb.stoppedPath
        ((min (LatticeProb.ConstantStepInterpolation.knot ⟨(R n) ^ 2, sq_nonneg (R n)⟩
          (Sandpile.exitTime (supBox (q n) (R n)) (X n ω)).toNat) (H n) : ℝ≥0) : ℝ≥0∞)
        (centeredWalkPath (R n) (q n) (X n ω)) := by
      funext n
      exact cubeStoppedWalk_eq_of_ne_top (hRpos n) (q n) (H n) (X n ω) (hw.2.1 n)
    have hy : Z₀ ω = LatticeProb.stoppedPath
        ((min (LatticeProb.openExitTime (fun t ω => Y ω t) (openUnitCube 0) ω).toNNReal h : ℝ≥0) : ℝ≥0∞)
        (Y ω) := cubeStoppedPath_eq_of_ne_top h (Y ω) hw.1
    rw [hz, hy]
    exact hw.2.2.2
  have hdist := tendstoInDistribution_of_ae_tendsto
    (fun n => (hZm n).aemeasurable) hZ₀m.aemeasurable hlim
  have hlaw (n : ℕ) : P.map (Z n) =
      (LatticeProb.siteWalkLaw d (q n)).map (cubeStoppedWalk (R n) (hRpos n) (q n) (H n)) := by
    change P.map (cubeStoppedWalk (R n) (hRpos n) (q n) (H n) ∘ X n) = _
    rw [← Measure.map_map (measurable_cubeStoppedWalk (R n) (hRpos n) (q n) (H n)) (hXm n), hXmap n]
    rfl
  have hlimitlaw : P.map Z₀ = PB.map (fun ω => cubeStoppedPath h (F ω)) := by
    change P.map (cubeStoppedPath h ∘ Y) = PB.map (cubeStoppedPath h ∘ F)
    rw [← Measure.map_map (measurable_cubeStoppedPath h) hYm, hYmap,
      Measure.map_map (measurable_cubeStoppedPath h) hFm]
  refine ⟨F, hFm, hF, ?_⟩
  refine ⟨fun n => (measurable_cubeStoppedWalk (R n) (hRpos n) (q n) (H n)).aemeasurable,
    ((measurable_cubeStoppedPath h).comp hFm).aemeasurable, ?_⟩
  have heq (n : ℕ) : (⟨P.map (Z n), (Measure.isProbabilityMeasure_map_iff (hZm n).aemeasurable).2 inferInstance⟩ :
      ProbabilityMeasure C(ℝ≥0, Continuum.Space d)) =
      ⟨(LatticeProb.siteWalkLaw d (q n)).map (cubeStoppedWalk (R n) (hRpos n) (q n) (H n)),
        (Measure.isProbabilityMeasure_map_iff (measurable_cubeStoppedWalk (R n) (hRpos n) (q n) (H n)).aemeasurable).2 inferInstance⟩ := by
    apply ProbabilityMeasure.toMeasure_injective
    exact hlaw n
  have heq₀ : (⟨P.map Z₀, (Measure.isProbabilityMeasure_map_iff hZ₀m.aemeasurable).2 inferInstance⟩ :
      ProbabilityMeasure C(ℝ≥0, Continuum.Space d)) =
      ⟨PB.map (fun ω => cubeStoppedPath h (F ω)),
        (Measure.isProbabilityMeasure_map_iff ((measurable_cubeStoppedPath h).comp hFm).aemeasurable).2 inferInstance⟩ := by
    apply ProbabilityMeasure.toMeasure_injective
    exact hlimitlaw
  simpa only [heq, heq₀] using hdist.tendsto

end Sandpile.External.Stopping
