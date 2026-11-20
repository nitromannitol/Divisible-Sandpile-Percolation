import Sandpile.External.Stopping.NaturalFiniteStoppingReward
import Sandpile.External.Stopping.StepRewardIntegrable
import Sandpile.External.Stopping.ApproximatedClockValue
import LatticeProb.Prob.BoundedStopping

/-!
# Density of finite right-continuous stopping rewards

Bounded natural stopping times can be approximated from above on a dyadic grid.
For right-continuous paths and bounded continuous rewards, their expectations converge.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- Every bounded natural stopping reward can be approximated by a finite-valued
natural stopping reward for right-continuous paths. -/
theorem exists_finite_natural_stop_reward_close_of_rightContinuous
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → Continuum.Space d) (hXm : ∀ t, Measurable (X t))
    (hXjoint : Measurable (fun p : ℝ≥0 × Ω => X p.1 p.2))
    (hXc : ∀ ω t, ContinuousWithinAt (fun s => X s ω) (Set.Ici t) t)
    (T : ℝ≥0) (τ : Ω → ℝ≥0) (hτ : Continuum.IsBrownianStopping X τ) (hτT : ∀ ω, τ ω ≤ T)
    (G : ℝ≥0 → Continuum.Space d → ℝ) (hGc : Continuous (fun p : ℝ≥0 × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ t z, |G t z| ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∃ σ : Ω → ℝ≥0, Continuum.IsBrownianStopping X σ ∧ (∀ ω, σ ω ≤ T) ∧
      (Set.range σ).Finite ∧
      |(∫ ω, G (σ ω) (X (σ ω) ω) ∂P) - (∫ ω, G (τ ω) (X (τ ω) ω) ∂P)| < ε := by
  let σ : ℕ → Ω → ℝ≥0 := fun n ω => min (LatticeProb.dyUp n (τ ω)) T
  have hσT : ∀ n ω, σ n ω ≤ T := fun _ _ => min_le_right _ _
  have hσstop : ∀ n, Continuum.IsBrownianStopping X (σ n) := by
    intro n
    have hs := (LatticeProb.isStoppingTime_dyUp hτ n).min_const T
    have heq : (fun ω => (σ n ω : ℝ≥0∞)) =
        (fun ω => min (LatticeProb.dyUp n (τ ω) : ℝ≥0∞) T) := by
      funext ω
      exact ENNReal.coe_min _ _
    change IsStoppingTime (Continuum.brownianFiltration X) (fun ω => (σ n ω : ℝ≥0∞))
    rw [heq]
    exact hs
  have hσfin : ∀ n, (Set.range (σ n)).Finite := by
    intro n
    let K := Nat.ceil ((2 ^ n : ℝ≥0) * T)
    refine ((Set.finite_Iic K).image (fun j : ℕ => min ((j : ℝ≥0) / 2 ^ n) T)).subset ?_
    rintro _ ⟨ω, rfl⟩
    refine ⟨Nat.ceil ((2 ^ n : ℝ≥0) * τ ω), ?_, ?_⟩
    · exact Nat.ceil_mono (mul_le_mul_of_nonneg_left (hτT ω) zero_le)
    · rfl
  have hσlim : ∀ ω, Tendsto (fun n => σ n ω) atTop (𝓝 (τ ω)) := by
    intro ω
    simpa only [σ, min_eq_left (hτT ω)] using
      (LatticeProb.tendsto_dyUp (τ ω)).min (tendsto_const_nhds (x := T))
  have hlim : Tendsto (fun n => ∫ ω, G (σ n ω) (X (σ n ω) ω) ∂P) atTop
      (𝓝 (∫ ω, G (τ ω) (X (τ ω) ω) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => M) (fun n => ?_)
      (integrable_const M) (fun n => ?_) ?_
    · have hσm : AEMeasurable (σ n) P :=
        (measurable_of_isBrownianStopping X hXm (σ n) (hσstop n)).aemeasurable
      have hp : AEMeasurable (fun ω => X (σ n ω) ω) P :=
        hXjoint.comp_aemeasurable (hσm.prodMk aemeasurable_id)
      exact (hGc.measurable.comp_aemeasurable (hσm.prodMk hp)).aestronglyMeasurable
    · filter_upwards with ω
      simpa only [Real.norm_eq_abs] using hG _ _
    · filter_upwards with ω
      have hwithin : Tendsto (fun n => σ n ω) atTop (𝓝[Set.Ici (τ ω)] (τ ω)) :=
        tendsto_nhdsWithin_iff.mpr ⟨hσlim ω, Filter.Eventually.of_forall fun n =>
          le_min (LatticeProb.le_dyUp n _) (hτT ω)⟩
      have hright : Tendsto (fun s => X s ω) (𝓝[Set.Ici (τ ω)] (τ ω))
          (𝓝 (X (τ ω) ω)) := hXc ω (τ ω)
      exact (hGc.tendsto _).comp ((hσlim ω).prodMk_nhds (hright.comp hwithin))
  have hnear := (Metric.tendsto_nhds.mp hlim) ε hε
  obtain ⟨n, hn⟩ := hnear.exists
  refine ⟨σ n, hσstop n, hσT n, hσfin n, ?_⟩
  simpa only [Real.dist_eq] using hn

end Sandpile.External.Stopping
