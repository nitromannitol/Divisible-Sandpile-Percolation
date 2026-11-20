import Sandpile.External.Stopping.KilledStoppingValueLowerLimit
import Sandpile.External.Stopping.CoupledStepLowerValue
import Sandpile.External.Stopping.NaturalStoppingComposition
import Sandpile.External.Stopping.UnkilledStepValue
import Sandpile.External.Stopping.CubeClockConstraint

/-!
# Lower killed-value bounds for coupled step walks

Convergent lattice stopping clocks can be used with the coupled step-walk
invariance principle to bound the killed value of the continuous limit.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- The killed value of the continuous limit is bounded by the lower limit of
coupled step-walk values when their natural stopping clocks converge. -/
theorem eventually_coupled_killed_step_value_ge_limit
    {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} [NeZero d] (R : ℕ → ℝ) (q : ℕ → Site d)
    (hRpos : ∀ n, 0 < R n) (hR : Tendsto R atTop atTop)
    (W : ℕ → Ω → (ℕ → Site d)) (Y : Ω → C(ℝ≥0, Continuum.Space d))
    (hWm : ∀ n, Measurable (W n)) (hYm : Measurable Y)
    (hWlaw : ∀ n, P.map (W n) = walkLaw d (q n))
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n => centeredWalkPath (R n) (q n) (W n ω)) atTop (𝓝 (Y ω)))
    (T : ℝ≥0) (κn : ℕ → (ℕ → Site d) → ℝ≥0)
    (hκn : ∀ n, Continuum.IsBrownianStopping (diffusiveStepWalk (R n)) (κn n))
    (hκlim : ∀ᵐ ω ∂P, Tendsto (fun n => κn n (W n ω)) atTop
      (𝓝 ((min (LatticeProb.openExitTime (fun t ω => Y ω t) (openUnitCube 0) ω)
        (T : ℝ≥0∞)).toNNReal)))
    (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ t z, |G t z| ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∃ F : ℕ → Filtration ℝ≥0 m,
      (∀ n t, F n t = Continuum.brownianFiltration
        (fun s ω => diffusiveStepWalk (R n) s (W n ω) - Lclt.scaledSite (R n) (q n)) t) ∧
      ∀ᶠ n in atTop,
        sSup (clockPayoffs (fun t ω => Y ω t) P T G
          (fun ω => (min (LatticeProb.openExitTime (fun t ω => Y ω t) (openUnitCube 0) ω)
            (T : ℝ≥0∞)).toNNReal) (Continuum.brownianFiltration (fun t ω => Y ω t))) ≤
        sSup (adaptedClockPayoffs (F n) P
          (fun t ω => diffusiveStepWalk (R n) t (W n ω) - Lclt.scaledSite (R n) (q n))
          T G (fun ω => κn n (W n ω))) + ε := by
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
  have hclock (n : ℕ) : IsStoppingTime (F n) (fun ω => (κn n (W n ω) : ℝ≥0∞)) := by
    have hc := isBrownianStopping_comp (diffusiveStepWalk (R n)) (W n) (κn n) (hκn n)
    have hc' := (isBrownianStopping_sub_const_iff
      (fun t ω => diffusiveStepWalk (R n) t (W n ω)) (Lclt.scaledSite (R n) (q n)) _).2 hc
    intro t
    rw [hF n t]
    exact hc' t
  refine ⟨F, hF, ?_⟩
  apply eventually_clock_value_le_adapted_clock_value_add P F T Xn (fun t ω => Y ω t)
    (fun t => (continuous_eval_const t).measurable.comp hYm) (fun ω => (Y ω).continuous)
    hXnm hAdapt ?_ (fun n ω => κn n (W n ω)) _ hclock
    (isBrownianStopping_openUnitCubeExitTrunc (fun t ω => Y ω t) (fun ω => (Y ω).continuous) 0 T)
    hκlim G hGc M hG ε hε
  exact ae_tendstoUniformlyOn_centered_diffusiveStepWalk P R q hRpos hR W Y hWm hWlaw hconv T

end Sandpile.External.Stopping
