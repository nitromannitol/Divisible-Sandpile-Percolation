import Sandpile.External.Stopping.ConditionalStoppingApproximation

/-!
# Reward convergence for approximated stopping times

For bounded continuous rewards, uniform path convergence and convergence in
probability of bounded stopping times imply convergence of stopped expectations.
This supplies the stopped-reward step in Coquet and Toldo, Section 2.2.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- Bounded stopped rewards converge when sample paths converge uniformly on a
finite horizon and stopping times converge in probability. -/
theorem tendsto_integral_reward_of_uniform_paths_and_stops
    {Ω E : Type*} [MeasurableSpace Ω] [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Xn : ℕ → ℝ≥0 → Ω → E) (X : ℝ≥0 → Ω → E) (H : ℝ≥0)
    (τn : ℕ → Ω → ℝ≥0) (τ : Ω → ℝ≥0)
    (hτn : ∀ n, AEMeasurable (τn n) P)
    (hYn : ∀ n, AEMeasurable (fun ω => Xn n (τn n ω) ω) P)
    (hbound : ∀ n ω, τn n ω ≤ H)
    (hτlim : TendstoInMeasure P τn atTop τ)
    (hpath : ∀ᵐ ω ∂P, Continuous (fun t => X t ω) ∧
      TendstoUniformlyOn (fun n t => Xn n t ω) (fun t => X t ω) atTop (Set.Icc 0 H))
    (G : ℝ≥0 → E → ℝ) (hGc : Continuous (fun p : ℝ≥0 × E => G p.1 p.2))
    (M : ℝ) (hG : ∀ t z, |G t z| ≤ M) :
    Tendsto (fun n => ∫ ω, G (τn n ω) (Xn n (τn n ω) ω) ∂P) atTop
      (𝓝 (∫ ω, G (τ ω) (X (τ ω) ω) ∂P)) := by
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms, hms, hstops⟩ := (hτlim.comp hns).exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  refine tendsto_integral_of_dominated_convergence (fun _ => M) (fun k => ?_)
    (integrable_const M) (fun k => ?_) ?_
  · exact (hGc.measurable.comp_aemeasurable
      ((hτn _).prodMk (hYn _))).aestronglyMeasurable
  · filter_upwards with ω
    simpa only [Real.norm_eq_abs] using hG _ _
  · filter_upwards [hstops, hpath] with ω hτconv hω
    have hidx : Tendsto (fun k => ns (ms k)) atTop atTop := hns.comp hms.tendsto_atTop
    have hpath' : TendstoUniformlyOn (fun k t => Xn (ns (ms k)) t ω)
        (fun t => X t ω) atTop (Set.Icc 0 H) := by
      intro U hU
      exact hidx.eventually (hω.2 U hU)
    have htime : Tendsto (fun k => τn (ns (ms k)) ω) atTop (𝓝[Set.Icc 0 H] (τ ω)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hτconv, Filter.Eventually.of_forall fun k =>
        ⟨bot_le, hbound (ns (ms k)) ω⟩⟩
    have hpos := hpath'.tendsto_comp (hω.1.continuousAt.continuousWithinAt) htime
    exact (hGc.tendsto _).comp (hτconv.prodMk_nhds hpos)

end Sandpile.External.Stopping
