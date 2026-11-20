import Sandpile.External.Stopping.BrownianPathLawTransfer
import Sandpile.External.Stopping.StepWalkIndependence

/-!
# Brownian motion on path space

The coordinate evaluation process under the law of a continuous Brownian
path is itself Brownian.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace Sandpile.External.Stopping

/-- The law of a continuous Brownian path makes path evaluation Brownian. -/
theorem isBrownian_eval_pathMap
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} [NeZero d]
    (P : Measure Ω) [IsProbabilityMeasure P] (a : Continuum.Space d)
    (B : ℝ≥0 → Ω → Continuum.Space d) (hB : Continuum.IsBrownian d a B P)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous fun t => B t ω) :
    Continuum.IsBrownian d a (fun t (f : C(ℝ≥0, Continuum.Space d)) => f t)
      (P.map (LatticeProb.pathMap B hc)) := by
  let F := LatticeProb.pathMap B hc
  have hFm : Measurable F := LatticeProb.measurable_pathMap B hm hc
  let : IsProbabilityMeasure (P.map F) :=
    (Measure.isProbabilityMeasure_map_iff hFm.aemeasurable).2 inferInstance
  refine ⟨?_, ?_, ?_⟩
  · apply (ae_map_iff hFm.aemeasurable ?_).2
    · exact hB.start
    · exact (isClosed_singleton.preimage (continuous_eval_const 0)).measurableSet
  · intro i
    let φ : C(ℝ≥0, Continuum.Space d) → ℝ≥0 → ℝ :=
      fun f t => Real.sqrt d * (f t i - a i)
    have hφm (t : ℝ≥0) : Measurable (fun f => φ f t) :=
      measurable_const.mul (((PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i).measurable.comp
        (continuous_eval_const t).measurable).sub measurable_const)
    have hφc (f : C(ℝ≥0, Continuum.Space d)) : Continuous (φ f) :=
      continuous_const.mul (((PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i).comp
        f.continuous).sub continuous_const)
    exact isBrownianReal_of_same_path_law hFm measurable_id (by rw [Measure.map_id]) φ hφm hφc (hB.coord i)
  · let f : Fin d → C(ℝ≥0, Continuum.Space d) → (ℝ≥0 → ℝ) :=
      fun i p t => p t i
    have hf (i : Fin d) : Measurable (f i) := measurable_pi_iff.2 fun t =>
      (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i).measurable.comp
        (continuous_eval_const t).measurable
    exact iIndepFun_map_of_comp P F hFm f hf hB.indep

end Sandpile.External.Stopping
