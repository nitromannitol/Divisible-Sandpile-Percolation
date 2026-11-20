import Sandpile.External.Stopping.FiniteNaturalRewardDensity

/-!
# Density of finite clipped stopping rewards

Finite dyadic approximations followed by clipping preserve bounded continuous
rewards of stopping times which lie before the clipping clock.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- A bounded natural stopping reward before a stopping clock is approximated
by rewards of finite natural stopping times clipped at that clock. -/
theorem exists_finite_natural_stop_clipped_reward_close
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → Continuum.Space d) (hXm : ∀ t, Measurable (X t))
    (hXc : ∀ ω, Continuous fun t => X t ω)
    (T : ℝ≥0) (τ κ : Ω → ℝ≥0) (hτ : Continuum.IsBrownianStopping X τ)
    (hκ : Continuum.IsBrownianStopping X κ) (hτT : ∀ ω, τ ω ≤ T)
    (hτκ : ∀ᵐ ω ∂P, τ ω ≤ κ ω)
    (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ t z, |G t z| ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∃ σ : Ω → ℝ≥0, Continuum.IsBrownianStopping X σ ∧ (∀ ω, σ ω ≤ T) ∧
      (Set.range σ).Finite ∧
      |(∫ ω, G ((T : ℝ) - min (σ ω) (κ ω)) (X (min (σ ω) (κ ω)) ω) ∂P) -
        (∫ ω, G ((T : ℝ) - τ ω) (X (τ ω) ω) ∂P)| < ε := by
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
  let ρ : ℕ → Ω → ℝ≥0 := fun n ω => min (σ n ω) (κ ω)
  have hρstop : ∀ n, Continuum.IsBrownianStopping X (ρ n) := by
    intro n
    change IsStoppingTime (Continuum.brownianFiltration X) (fun ω => (ρ n ω : ℝ≥0∞))
    have heq : (fun ω => (ρ n ω : ℝ≥0∞)) =
        (fun ω => min (σ n ω : ℝ≥0∞) (κ ω : ℝ≥0∞)) := by
      funext ω
      exact ENNReal.coe_min _ _
    rw [heq]
    exact (hσstop n).min hκ
  have hρlim : ∀ᵐ ω ∂P, Tendsto (fun n => ρ n ω) atTop (𝓝 (τ ω)) := by
    filter_upwards [hτκ] with ω hω
    have hs : Tendsto (fun n => σ n ω) atTop (𝓝 (τ ω)) := by
      simpa only [σ, min_eq_left (hτT ω)] using
        (LatticeProb.tendsto_dyUp (τ ω)).min (tendsto_const_nhds (x := T))
    simpa only [ρ, min_eq_left hω] using hs.min (tendsto_const_nhds (x := κ ω))
  have hlim := tendsto_integral_reward_of_ae_tendsto P X (fun t => (hXm t).aemeasurable)
    (Filter.Eventually.of_forall hXc) ρ τ
    (fun n => Continuum.IsBrownianStopping.aemeasurable (hρstop n) P (fun t => (hXm t).aemeasurable))
    hρlim T M G hGc hG
  have hnear := (Metric.tendsto_nhds.mp hlim) ε hε
  obtain ⟨n, hn⟩ := hnear.exists
  refine ⟨σ n, hσstop n, hσT n, hσfin n, ?_⟩
  simpa only [Real.dist_eq] using hn

end Sandpile.External.Stopping
