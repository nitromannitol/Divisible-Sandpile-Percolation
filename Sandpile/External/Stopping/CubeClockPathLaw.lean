import Sandpile.External.Stopping.KilledValuePullback
import Sandpile.External.Stopping.CubeClockConstraint

/-!
# Cube-clock values and continuous path laws

The value stopped at the open-cube exit depends only on the law of the
continuous path.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace Sandpile.External.Stopping

/-- Cube-clock values agree for random continuous paths with the same law. -/
theorem cubeClockValue_eq_of_path_law_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure Ω') [IsProbabilityMeasure Q]
    (Y : Ω → C(ℝ≥0, Continuum.Space d)) (F : Ω' → C(ℝ≥0, Continuum.Space d))
    (hYm : Measurable Y) (hFm : Measurable F) (hlaw : P.map Y = Q.map F)
    (x : Continuum.Space d) (T : ℝ≥0) (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ s z, |G s z| ≤ M) :
    sSup (clockPayoffs (fun t ω => Y ω t) P T G
      (fun ω => (min (LatticeProb.openExitTime (fun t ω => Y ω t) (openUnitCube x) ω)
        (T : ℝ≥0∞)).toNNReal) (Continuum.brownianFiltration (fun t ω => Y ω t))) =
    sSup (clockPayoffs (fun t ω => F ω t) Q T G
      (fun ω => (min (LatticeProb.openExitTime (fun t ω => F ω t) (openUnitCube x) ω)
        (T : ℝ≥0∞)).toNNReal) (Continuum.brownianFiltration (fun t ω => F ω t))) := by
  let E : ℝ≥0 → C(ℝ≥0, Continuum.Space d) → Continuum.Space d := fun t f => f t
  let κ : C(ℝ≥0, Continuum.Space d) → ℝ≥0 := fun f =>
    (min (LatticeProb.openExitTime E (openUnitCube x) f) (T : ℝ≥0∞)).toNNReal
  have hEm : ∀ t, StronglyMeasurable (E t) := fun t => (continuous_eval_const t).stronglyMeasurable
  have hEj : Measurable (fun p : ℝ≥0 × C(ℝ≥0, Continuum.Space d) => E p.1 p.2) :=
    continuous_eval.measurable.comp (measurable_snd.prodMk measurable_fst)
  have hEc : ∀ f t, ContinuousWithinAt (fun s => E s f) (Set.Ici t) t :=
    fun f t => f.continuous.continuousAt.continuousWithinAt
  have hκ : Continuum.IsBrownianStopping E κ :=
    isBrownianStopping_openUnitCubeExitTrunc E (fun f => f.continuous) x T
  let μ := P.map Y
  let : IsProbabilityMeasure μ := (Measure.isProbabilityMeasure_map_iff hYm.aemeasurable).2 inferInstance
  have hY := clockStoppingValue_eq_of_map P μ E hEm hEj hEc Y hYm rfl T κ hκ G hGc M hG
  have hF := clockStoppingValue_eq_of_map Q μ E hEm hEj hEc F hFm hlaw.symm T κ hκ G hGc M hG
  exact hY.trans hF.symm

end Sandpile.External.Stopping
