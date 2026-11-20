import Sandpile.External.Stopping.StoppingValueLowerLimit
import Sandpile.External.Stopping.CoupledStepWalkConvergence

/-!
# Lower stopping-value bound for coupled step walks

The lower value inequality applies to the centered step walks in the
Skorokhod coupling with Brownian paths.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- Coupled centered step walks have asymptotic stopping values at least as
large as the natural stopping value of their continuous limit. -/
theorem eventually_coupled_step_value_ge_limit
    {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} [NeZero d] (R : ℕ → ℝ) (q : ℕ → Site d)
    (hRpos : ∀ n, 0 < R n) (hR : Tendsto R atTop atTop)
    (W : ℕ → Ω → (ℕ → Site d)) (Y : Ω → C(ℝ≥0, Continuum.Space d))
    (hWm : ∀ n, Measurable (W n)) (hYm : Measurable Y)
    (hWlaw : ∀ n, P.map (W n) = walkLaw d (q n))
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n => centeredWalkPath (R n) (q n) (W n ω)) atTop (𝓝 (Y ω)))
    (T : ℝ≥0) (G : ℝ≥0 → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ≥0 × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ t z, |G t z| ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∃ F : ℕ → Filtration ℝ≥0 m,
      (∀ n t, F n t = Continuum.brownianFiltration
        (fun s ω => diffusiveStepWalk (R n) s (W n ω) - Lclt.scaledSite (R n) (q n)) t) ∧
      ∀ᶠ n in atTop, sSup (naturalStoppingPayoffs P (fun t ω => Y ω t) T G) ≤
        sSup (filtrationStoppingPayoffs (F n) P
          (fun t ω => diffusiveStepWalk (R n) t (W n ω) - Lclt.scaledSite (R n) (q n)) T G) + ε := by
  let Xn : ℕ → ℝ≥0 → Ω → Continuum.Space d := fun n t ω =>
    diffusiveStepWalk (R n) t (W n ω) - Lclt.scaledSite (R n) (q n)
  have hXnm : ∀ n, Measurable (fun p : ℝ≥0 × Ω => Xn n p.1 p.2) := by
    intro n
    exact ((measurable_diffusiveStepWalk_uncurry (R n)).comp
      (measurable_fst.prodMk ((hWm n).comp measurable_snd))).sub_const _
  have hm (n : ℕ) (t : ℝ≥0) : StronglyMeasurable (Xn n t) :=
    ((hXnm n).comp (measurable_const.prodMk measurable_id)).stronglyMeasurable
  let F : ℕ → Filtration ℝ≥0 m := fun n => LatticeProb.natFiltration (Xn n) (hm n)
  have hF : ∀ n t, F n t = Continuum.brownianFiltration (Xn n) t := by
    intro n t
    rfl
  have hAdapt : ∀ n t, @Measurable Ω (Continuum.Space d) (F n t) inferInstance (Xn n t) := by
    intro n t
    exact (LatticeProb.stronglyAdapted_natFiltration (Xn n) (hm n) t).measurable
  refine ⟨F, hF, ?_⟩
  apply eventually_natural_value_le_adapted_value_add P F T Xn (fun t ω => Y ω t)
    (fun t => (continuous_eval_const t).measurable.comp hYm) (fun ω => (Y ω).continuous)
    hXnm hAdapt ?_ G hGc M hG ε hε
  exact ae_tendstoUniformlyOn_centered_diffusiveStepWalk P R q hRpos hR W Y hWm hWlaw hconv T

end Sandpile.External.Stopping
