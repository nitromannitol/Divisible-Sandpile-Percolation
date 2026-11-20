import Sandpile.External.Stopping.FiniteNaturalStoppingApproximation
import Sandpile.External.Stopping.ClippedStoppingRewardLimit

/-!
# Approximation of clipped finite stopping rewards

Finite natural stopping rules can be transferred to convergent adapted
processes and clipped by convergent stopping clocks.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- A finite natural stopping rule, clipped by a limiting clock, has rewards
approximated by stopping rules clipped by convergent stopping clocks. -/
theorem exists_clipped_finite_natural_stopping_reward_approx
    {Ω : Type*} [m : MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℕ → Filtration ℝ≥0 m) (T : ℝ≥0) (V : Finset ℝ≥0)
    (hVT : ∀ t ∈ V, t ≤ T) (τ : Ω → ℝ≥0) (hτV : ∀ ω, τ ω ∈ V)
    (Xn : ℕ → ℝ≥0 → Ω → Continuum.Space d) (X : ℝ≥0 → Ω → Continuum.Space d)
    (hτ : Continuum.IsBrownianStopping X τ)
    (hX : ∀ t, Measurable (X t)) (hXc : ∀ ω, Continuous fun t => X t ω)
    (hXn : ∀ n, Measurable (fun p : ℝ≥0 × Ω => Xn n p.1 p.2))
    (hXadapt : ∀ n t, @Measurable Ω (Continuum.Space d) (F n t) inferInstance (Xn n t))
    (hpath : ∀ᵐ ω ∂P,
      TendstoUniformlyOn (fun n t => Xn n t ω) (fun t => X t ω) atTop (Set.Icc 0 T))
    (κn : ℕ → Ω → ℝ≥0) (κ : Ω → ℝ≥0)
    (hκn : ∀ n, IsStoppingTime (F n) (fun ω => (κn n ω : ℝ≥0∞)))
    (hκlim : ∀ᵐ ω ∂P, Tendsto (fun n => κn n ω) atTop (𝓝 (κ ω)))
    (G : ℝ≥0 → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ≥0 × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ t z, |G t z| ≤ M) :
    ∃ ρ : ℕ → Ω → ℝ≥0,
      (∀ n, IsStoppingTime (F n) (fun ω => (ρ n ω : ℝ≥0∞))) ∧
      (∀ n ω, ρ n ω ≤ T) ∧ (∀ n ω, ρ n ω ≤ κn n ω) ∧
      Tendsto (fun n => ∫ ω, G (ρ n ω) (Xn n (ρ n ω) ω) ∂P) atTop
        (𝓝 (∫ ω, G (min (τ ω) (κ ω)) (X (min (τ ω) (κ ω)) ω) ∂P)) := by
  obtain ⟨τn, hτn, hτnT, hτlim⟩ :=
    exists_finite_natural_stopping_approx_inMeasure P F T V hVT τ hτV Xn X
      hτ hX hXc hXadapt hpath
  have hτnm : ∀ n, Measurable (τn n) := by
    intro n
    exact measurable_coe_nnreal_ennreal_iff.mp
      ((hτn n).measurable.mono (hτn n).measurableSpace_le le_rfl)
  have hκnm : ∀ n, Measurable (κn n) := by
    intro n
    exact measurable_coe_nnreal_ennreal_iff.mp
      ((hκn n).measurable.mono (hκn n).measurableSpace_le le_rfl)
  let ρ : ℕ → Ω → ℝ≥0 := fun n ω => min (τn n ω) (κn n ω)
  have hρstop : ∀ n, IsStoppingTime (F n) (fun ω => (ρ n ω : ℝ≥0∞)) := by
    intro n
    have heq : (fun ω => (ρ n ω : ℝ≥0∞)) =
        (fun ω => min (τn n ω : ℝ≥0∞) (κn n ω : ℝ≥0∞)) := by
      funext ω
      exact ENNReal.coe_min _ _
    rw [heq]
    exact (hτn n).min (hκn n)
  have hρm : ∀ n, Measurable (ρ n) := fun n => (hτnm n).min (hκnm n)
  have hXstop : ∀ n, AEMeasurable (fun ω => Xn n (ρ n ω) ω) P := fun n =>
    ((hXn n).comp ((hρm n).prodMk measurable_id)).aemeasurable
  refine ⟨ρ, hρstop, (fun n ω => (min_le_left _ _).trans (hτnT n ω)),
    (fun n ω => min_le_right _ _), ?_⟩
  exact tendsto_integral_reward_of_clipped_stops P Xn X T τn κn τ κ
    (fun n => (hτnm n).aemeasurable) (fun n => (hκnm n).aemeasurable)
    hXstop (fun n ω => (min_le_left _ _).trans (hτnT n ω)) hτlim hκlim
    (hpath.mono fun ω hω => ⟨hXc ω, hω⟩) G hGc M hG

end Sandpile.External.Stopping
