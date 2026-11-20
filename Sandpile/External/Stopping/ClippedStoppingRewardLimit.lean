import Sandpile.External.Stopping.ConvergentStoppingRewards

/-!
# Convergence of clipped stopping rewards

A convergent killing clock may be combined with stopping times converging in
probability when passing to the limit in bounded continuous stopped rewards.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- Bounded rewards converge when stopping times converge in probability, the
clipping clocks converge almost surely, and the paths converge uniformly. -/
theorem tendsto_integral_reward_of_clipped_stops
    {Ω E : Type*} [MeasurableSpace Ω] [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Xn : ℕ → ℝ≥0 → Ω → E) (X : ℝ≥0 → Ω → E) (H : ℝ≥0)
    (τn κn : ℕ → Ω → ℝ≥0) (τ κ : Ω → ℝ≥0)
    (hτn : ∀ n, AEMeasurable (τn n) P)
    (hκn : ∀ n, AEMeasurable (κn n) P)
    (hYn : ∀ n, AEMeasurable (fun ω => Xn n (min (τn n ω) (κn n ω)) ω) P)
    (hbound : ∀ n ω, min (τn n ω) (κn n ω) ≤ H)
    (hτlim : TendstoInMeasure P τn atTop τ)
    (hκlim : ∀ᵐ ω ∂P, Tendsto (fun n => κn n ω) atTop (𝓝 (κ ω)))
    (hpath : ∀ᵐ ω ∂P, Continuous (fun t => X t ω) ∧
      TendstoUniformlyOn (fun n t => Xn n t ω) (fun t => X t ω) atTop (Set.Icc 0 H))
    (G : ℝ≥0 → E → ℝ) (hGc : Continuous (fun p : ℝ≥0 × E => G p.1 p.2))
    (M : ℝ) (hG : ∀ t z, |G t z| ≤ M) :
    Tendsto (fun n => ∫ ω, G (min (τn n ω) (κn n ω))
      (Xn n (min (τn n ω) (κn n ω)) ω) ∂P) atTop
      (𝓝 (∫ ω, G (min (τ ω) (κ ω)) (X (min (τ ω) (κ ω)) ω) ∂P)) := by
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms, hms, hstops⟩ := (hτlim.comp hns).exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  refine tendsto_integral_of_dominated_convergence (fun _ => M) (fun k => ?_)
    (integrable_const M) (fun k => ?_) ?_
  · exact (hGc.measurable.comp_aemeasurable
      (((hτn _).min (hκn _)).prodMk (hYn _))).aestronglyMeasurable
  · filter_upwards with ω
    simpa only [Real.norm_eq_abs] using hG _ _
  · filter_upwards [hstops, hκlim, hpath] with ω hτconv hκconv hω
    have hidx : Tendsto (fun k => ns (ms k)) atTop atTop := hns.comp hms.tendsto_atTop
    have hpath' : TendstoUniformlyOn (fun k t => Xn (ns (ms k)) t ω)
        (fun t => X t ω) atTop (Set.Icc 0 H) := by
      intro U hU
      exact hidx.eventually (hω.2 U hU)
    have htime := hτconv.min (hκconv.comp hidx)
    have htime' : Tendsto (fun k => min (τn (ns (ms k)) ω) (κn (ns (ms k)) ω))
        atTop (𝓝[Set.Icc 0 H] (min (τ ω) (κ ω))) :=
      tendsto_nhdsWithin_iff.mpr ⟨htime, Filter.Eventually.of_forall fun k =>
        ⟨bot_le, hbound (ns (ms k)) ω⟩⟩
    have hpos := hpath'.tendsto_comp (hω.1.continuousAt.continuousWithinAt) htime'
    exact (hGc.tendsto _).comp (htime.prodMk_nhds hpos)

end Sandpile.External.Stopping
