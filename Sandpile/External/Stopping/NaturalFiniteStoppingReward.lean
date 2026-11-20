import Sandpile.External.Stopping.ObservedFiniteStoppingReward
import Sandpile.External.Stopping.RationalHistory

/-!
# Finite stopping rewards for convergent natural filtrations

Countable rational histories turn a finite natural stopping rule of a continuous
limit process into Borel decision events of convergent adapted observations.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- Finite natural stopping rewards of a continuous process are limits of
stopping rewards for uniformly convergent adapted processes. -/
theorem exists_finite_natural_stopping_reward_approx
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
    (G : ℝ≥0 → Continuum.Space d → ℝ) (hGc : Continuous (fun p : ℝ≥0 × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ t z, |G t z| ≤ M) :
    ∃ τn : ℕ → Ω → ℝ≥0,
      (∀ n, IsStoppingTime (F n) (fun ω => (τn n ω : ℝ≥0∞))) ∧
      (∀ n ω, τn n ω ≤ T) ∧
      Tendsto (fun n => ∫ ω, G (τn n ω) (Xn n (τn n ω) ω) ∂P) atTop
        (𝓝 (∫ ω, G (τ ω) (X (τ ω) ω) ∂P)) := by
  let O := ℚ → Continuum.Space d
  let := TopologicalSpace.upgradeIsCompletelyMetrizable O
  let Y : ℝ≥0 → Ω → O := rationalHistory X
  let Yn : ℕ → ℝ≥0 → Ω → O := fun n => rationalHistory (Xn n)
  have hYm : ∀ t ∈ V, Measurable (Y t) := by
    intro t ht
    apply measurable_pi_iff.2
    intro q
    exact hX _
  have hYnm : ∀ n, ∀ t ∈ V, @Measurable Ω O (F n t) inferInstance (Yn n t) := by
    intro n t ht
    let : MeasurableSpace Ω := F n t
    apply measurable_pi_iff.2
    intro q
    exact (hXadapt n _).mono ((F n).mono (min_le_right _ _)) le_rfl
  have hYconv : ∀ t ∈ V, ∀ᵐ ω ∂P, Tendsto (fun n => Yn n t ω) atTop (𝓝 (Y t ω)) := by
    intro t ht
    filter_upwards [hpath] with ω hω
    apply tendsto_pi_nhds.2
    intro q
    exact hω.tendsto_at ⟨bot_le, (min_le_right _ _).trans (hVT t ht)⟩
  have hrepresent (t : ℝ≥0) : ∃ S : Set O, MeasurableSet S ∧
      {ω | τ ω = t} = Y t ⁻¹' S := by
    have he := hτ.measurableSet_eq t
    change MeasurableSet[Continuum.brownianFiltration X t] {ω | (τ ω : ℝ≥0∞) = (t : ℝ≥0∞)} at he
    have heq : {ω | (τ ω : ℝ≥0∞) = (t : ℝ≥0∞)} = {ω | τ ω = t} := by
      ext ω
      exact ENNReal.coe_inj
    rw [heq] at he
    obtain ⟨S, hS, heS⟩ := exists_rationalHistory_event X hXc t {ω | τ ω = t} he
    exact ⟨S, hS, heS.symm⟩
  choose S hSm hS using hrepresent
  apply exists_finite_stopping_reward_approx_of_observations P F T V hVT τ hτV Y Yn
    hYm hYnm hYconv S (fun t _ => hSm t) (fun t _ => hS t) Xn X hXn ?_ G hGc M hG
  filter_upwards [hpath] with ω hω
  exact ⟨hXc ω, hω⟩

end Sandpile.External.Stopping
